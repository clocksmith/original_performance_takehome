from __future__ import annotations

import json
import random
import sys
from dataclasses import dataclass
from importlib import util
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from perf_takehome import KernelBuilder


def _load_problem(use_frozen: bool):
    if use_frozen:
        from tests import frozen_problem as problem_mod
    else:
        import problem as problem_mod
    return problem_mod


@dataclass
class Env:
    env_id: int
    problem: Any
    mem0: list[int]
    program: list[dict]
    debug_info: Any
    machine: Any
    forest_height: int
    batch_size: int
    rounds: int
    seed: int
    enable_debug: bool
    trace: bool


_ENVS: dict[int, Env] = {}
_NEXT_ID = 0

_VARIANTS: dict[str, Path | None] = {
    "default": None,
    "kernel_builder_override": ROOT / "kernel_builder_override.py",
    "cache_top4_d4x15_reset_offload_1013": ROOT / "cache_top4_d4x15_reset_offload_1013.py",
    "cache_top4_d4x15_reset_offload_1015_full_window": ROOT / "cache_top4_d4x15_reset_offload_1015_full_window.py",
    "cache_top4_d4x15_reset_offload_1016": ROOT / "cache_top4_d4x15_reset_offload_1016.py",
    "loadbound_preload15_uncached_1316": ROOT / "loadbound_preload15_uncached_1316.py",
}


def _new_env_id() -> int:
    global _NEXT_ID
    env_id = _NEXT_ID
    _NEXT_ID += 1
    return env_id


def _require_env(env_id: int) -> Env:
    if env_id not in _ENVS:
        raise ValueError(f"unknown env_id {env_id}")
    return _ENVS[env_id]


def _load_kernel_builder(variant: str):
    if variant not in _VARIANTS:
        raise ValueError(f"unknown variant '{variant}'")
    path = _VARIANTS[variant]
    if path is None:
        return KernelBuilder
    if not path.exists():
        raise FileNotFoundError(f"KernelBuilder override not found: {path}")
    module_name = f"kernel_builder_{variant}"
    spec = util.spec_from_file_location(module_name, str(path))
    if spec is None or spec.loader is None:
        raise ImportError(f"Failed to load KernelBuilder override: {path}")
    module = util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    if not hasattr(module, "KernelBuilder"):
        raise AttributeError("KernelBuilder override module must define `KernelBuilder`.")
    return module.KernelBuilder


def _run_machine(machine: Any, max_cycles: int | None, max_instructions: int | None) -> int:
    for core in machine.cores:
        if core.state == core.state.PAUSED:
            core.state = core.state.RUNNING

    steps = 0
    while any(c.state == c.state.RUNNING for c in machine.cores):
        if max_instructions is not None and steps >= max_instructions:
            break
        if max_cycles is not None and machine.cycle >= max_cycles:
            break

        has_non_debug = False
        for core in machine.cores:
            if core.state != core.state.RUNNING:
                continue
            if core.pc >= len(machine.program):
                core.state = core.state.STOPPED
                continue
            instr = machine.program[core.pc]
            if machine.prints:
                machine.print_step(instr, core)
            core.pc += 1
            machine.step(instr, core)
            if any(name != "debug" for name in instr.keys()):
                has_non_debug = True

        if has_non_debug:
            machine.cycle += 1
        steps += 1

    return steps


def _build_value_trace(problem: Any, mem: list[int]) -> dict[Any, int]:
    trace: dict[Any, int] = {}
    mem_copy = mem.copy()
    for _ in problem.reference_kernel2(mem_copy, trace):
        pass
    return trace


def get_limits() -> dict[str, Any]:
    """Return ISA limits and constants."""
    problem = _load_problem(use_frozen=False)
    return {
        "slot_limits": problem.SLOT_LIMITS,
        "vlen": problem.VLEN,
        "n_cores": problem.N_CORES,
        "scratch_size": problem.SCRATCH_SIZE,
    }


def list_variants() -> dict[str, Any]:
    """
    List available kernel builder variants.

    Returns:
        variants: List of variant names.
        paths: Mapping from variant name to file path (or null for default).
    """
    return {
        "variants": sorted(_VARIANTS.keys()),
        "paths": {name: (str(path) if path is not None else None) for name, path in _VARIANTS.items()},
    }


def sweep_caps(
    T_values: list[int] | None = None,
    flow_setup_ops: list[int] | None = None,
    shift_on_alu: list[bool] | None = None,
    reset_on_flow: list[bool] | None = None,
    depth4_rounds: list[int] | None = None,
    setup_valu: list[int] | None = None,
    x_values: list[int] | None = None,
    sort_by: str = "setup_slack",
    max_results_per_config: int | None = 20,
) -> dict[str, Any]:
    """
    Sweep cache/offload parameter combos against ISA caps.

    Args:
        T_values: Cycle budgets to test (default [1013, 1016]).
        flow_setup_ops: Flow setup op counts (default [0, 64]).
        shift_on_alu: Whether shifts are on ALU (default [False, True]).
        reset_on_flow: Whether reset is on Flow (default [False, True]).
        depth4_rounds: Depth-4 caching rounds (default [0, 1, 2]).
        setup_valu: Setup VALU op counts (default [0, 16, 32, 48]).
        x_values: Cached vector counts X (default 0..32).
        sort_by: Field to sort results by.
        max_results_per_config: Max results per config (None for all).
    """
    VEC = 32
    ROUNDS = 16
    VLEN = 8

    HASH_VALU_PER_VEC = 12 * ROUNDS
    NODE_XOR_PER_VEC = ROUNDS
    PARITY_ROUNDS = ROUNDS - 2
    IDX_UPDATE_ROUNDS = ROUNDS - 2
    RESET_VALU_OPS = 1
    BASE_VALU_PER_VEC = (
        HASH_VALU_PER_VEC
        + NODE_XOR_PER_VEC
        + PARITY_ROUNDS
        + IDX_UPDATE_ROUNDS
    )
    MAX_OFFLOAD = 3 * ROUNDS * VEC

    BASE_CACHED_NODES = 15
    LEVEL4_NODES = 16
    BASE_CACHED_ROUNDS = 8

    VSELECTS_PER_DEPTH = {0: 0, 1: 1, 2: 3, 3: 7, 4: 15}
    FLOW_BASE_TOP4 = VEC * 2 * sum(VSELECTS_PER_DEPTH[d] for d in range(0, 4))
    FLOW_PTR_SETUP = 64
    FLOW_PER_VEC_DEPTH4 = VSELECTS_PER_DEPTH[4]

    VLOADS = 64

    if T_values is None:
        T_values = [1013, 1016]
    if flow_setup_ops is None:
        flow_setup_ops = [0, FLOW_PTR_SETUP]
    if shift_on_alu is None:
        shift_on_alu = [False, True]
    if reset_on_flow is None:
        reset_on_flow = [False, True]
    if depth4_rounds is None:
        depth4_rounds = [0, 1, 2]
    if setup_valu is None:
        setup_valu = [0, 16, 32, 48]

    def compute_load_ops(depth4: int, x: int) -> int:
        uncached_full_rounds = ROUNDS - BASE_CACHED_ROUNDS - depth4
        cached_nodes = BASE_CACHED_NODES + (LEVEL4_NODES if x > 0 else 0)
        full_uncached = uncached_full_rounds * VEC * VLEN
        partial_uncached = depth4 * (VEC - x) * VLEN
        return VLOADS + cached_nodes + full_uncached + partial_uncached

    if x_values is None:
        x_values = list(range(0, VEC + 1))

    def sort_key(item: dict[str, Any]):
        if sort_by in item:
            return item[sort_by]
        return item.get("setup_slack", 0)

    configs: list[dict[str, Any]] = []
    for flow_setup in flow_setup_ops:
        for shift in shift_on_alu:
            for reset in reset_on_flow:
                for depth4 in depth4_rounds:
                    for setup in setup_valu:
                        for T in T_values:
                            valu_cap = 6 * T
                            alu_cap = 12 * T
                            load_cap = 2 * T
                            flow_cap = T

                            flow_base = FLOW_BASE_TOP4 + flow_setup
                            shift_ops = 3 * ROUNDS * VEC
                            shift_alu_ops = shift_ops * VLEN if shift else 0
                            reset_valu_ops = 0 if reset else RESET_VALU_OPS
                            reset_flow_ops = VEC if reset else 0

                            results = []
                            for X in x_values:
                                load_ops = compute_load_ops(depth4, X)
                                flow_ops = flow_base + FLOW_PER_VEC_DEPTH4 * X * depth4 + reset_flow_ops

                                total_valu = (
                                    BASE_VALU_PER_VEC * VEC
                                    + reset_valu_ops * VEC
                                    + setup
                                    - (shift_ops if shift else 0)
                                )
                                min_offload = max(0, total_valu - valu_cap)
                                if min_offload > MAX_OFFLOAD:
                                    continue

                                alu_ops = min_offload * VLEN + shift_alu_ops
                                valu_ops = total_valu - min_offload

                                if load_ops > load_cap:
                                    continue
                                if flow_ops > flow_cap:
                                    continue
                                if alu_ops > alu_cap:
                                    continue
                                if valu_ops > valu_cap:
                                    continue

                                alu_slack = alu_cap - alu_ops
                                extra_offload = min(alu_slack // VLEN, MAX_OFFLOAD - min_offload)
                                setup_slack = extra_offload

                                results.append(
                                    {
                                        "T": T,
                                        "X": X,
                                        "depth4_rounds": depth4,
                                        "flow_ops": flow_ops,
                                        "load_ops": load_ops,
                                        "min_offload": min_offload,
                                        "alu_ops": alu_ops,
                                        "valu_ops": valu_ops,
                                        "setup_slack": setup_slack,
                                    }
                                )

                            if not results:
                                continue

                            results_sorted = sorted(results, key=sort_key, reverse=True)
                            if max_results_per_config is not None:
                                results_sorted = results_sorted[:max_results_per_config]

                            configs.append(
                                {
                                    "T": T,
                                    "flow_setup": flow_setup,
                                    "shift_on_alu": shift,
                                    "reset_on_flow": reset,
                                    "depth4_rounds": depth4,
                                    "setup_valu": setup,
                                    "results": results_sorted,
                                }
                            )

    return {"configs": configs}


def run_variant(
    variant: str,
    forest_height: int = 10,
    rounds: int = 16,
    batch_size: int = 256,
    seed: int | None = 0,
    use_frozen: bool = True,
    check_correctness: bool = True,
) -> dict[str, Any]:
    """
    Run a kernel builder variant and return cycles + correctness.

    Args:
        variant: Variant name from list_variants().
        forest_height: Tree height.
        rounds: Number of rounds.
        batch_size: Number of inputs.
        seed: RNG seed for deterministic inputs (None for random).
        use_frozen: If True, use tests/frozen_problem semantics.
        check_correctness: If True, validate output values via reference kernel.
    """
    if seed is not None:
        random.seed(seed)

    problem = _load_problem(use_frozen)
    forest = problem.Tree.generate(forest_height)
    inp = problem.Input.generate(forest, batch_size, rounds)
    mem = problem.build_mem_image(forest, inp)

    try:
        builder_cls = _load_kernel_builder(variant)
        kb = builder_cls()
        kb.build_kernel(forest.height, len(forest.values), len(inp.indices), rounds)
    except Exception as exc:
        return {"variant": variant, "ok": False, "error": f"{type(exc).__name__}: {exc}"}

    machine = problem.Machine(mem, kb.instrs, kb.debug_info(), n_cores=problem.N_CORES)
    machine.enable_pause = False
    machine.enable_debug = False
    machine.run()

    if check_correctness:
        ref_mem = None
        for ref_mem in problem.reference_kernel2(mem):
            pass
        if ref_mem is None:
            return {"variant": variant, "ok": False, "error": "reference kernel produced no output"}
        inp_values_p = ref_mem[6]
        expected = ref_mem[inp_values_p : inp_values_p + len(inp.values)]
        actual = machine.mem[inp_values_p : inp_values_p + len(inp.values)]
        if actual != expected:
            return {
                "variant": variant,
                "ok": False,
                "cycle": machine.cycle,
                "error": "Incorrect output values",
            }

    return {
        "variant": variant,
        "ok": True,
        "cycle": machine.cycle,
        "program_len": len(kb.instrs),
    }


def compare_variants(
    variants: list[str] | None = None,
    forest_height: int = 10,
    rounds: int = 16,
    batch_size: int = 256,
    seed: int | None = 0,
    use_frozen: bool = True,
    check_correctness: bool = True,
) -> dict[str, Any]:
    """
    Run multiple variants and return a sorted summary by cycle count.

    Args:
        variants: List of variant names (None for all).
        forest_height: Tree height.
        rounds: Number of rounds.
        batch_size: Number of inputs.
        seed: RNG seed for deterministic inputs (None for random).
        use_frozen: If True, use tests/frozen_problem semantics.
        check_correctness: If True, validate output values via reference kernel.
    """
    if variants is None:
        variants = sorted(_VARIANTS.keys())
    results = []
    for name in variants:
        results.append(
            run_variant(
                name,
                forest_height=forest_height,
                rounds=rounds,
                batch_size=batch_size,
                seed=seed,
                use_frozen=use_frozen,
                check_correctness=check_correctness,
            )
        )

    def sort_key(item: dict[str, Any]) -> tuple[int, int]:
        if item.get("ok") and item.get("cycle") is not None:
            return (0, item["cycle"])
        return (1, 10**9)

    results_sorted = sorted(results, key=sort_key)
    best = next((r for r in results_sorted if r.get("ok")), None)
    return {"results": results_sorted, "best": best}


def make_env(
    forest_height: int,
    batch_size: int,
    rounds: int,
    seed: int = 0,
    enable_debug: bool = False,
    trace: bool = False,
    use_frozen: bool = False,
) -> dict[str, Any]:
    """
    Create a Machine environment with a KernelBuilder program.

    Args:
        forest_height: Tree height for the forest.
        batch_size: Number of input items to process.
        rounds: Number of traversal rounds.
        seed: RNG seed for generating tree values and inputs.
        enable_debug: If True, populate debug trace values.
        trace: If True, enable Chrome trace output.
        use_frozen: If True, use tests/frozen_problem.py semantics.

    Returns a new env_id and basic metadata.
    """
    problem = _load_problem(use_frozen)

    random.seed(seed)
    t = problem.Tree.generate(forest_height)
    inp = problem.Input.generate(t, batch_size, rounds)
    mem = problem.build_mem_image(t, inp)

    n_nodes = 2 ** (forest_height + 1) - 1
    builder = KernelBuilder()
    builder.build_kernel(forest_height, n_nodes, batch_size, rounds)

    debug_info = builder.debug_info()
    value_trace = _build_value_trace(problem, mem) if enable_debug else {}

    machine = problem.Machine(
        mem,
        builder.instrs,
        debug_info,
        n_cores=problem.N_CORES,
        scratch_size=problem.SCRATCH_SIZE,
        trace=trace,
        value_trace=value_trace,
    )
    if not enable_debug:
        machine.enable_debug = False

    env_id = _new_env_id()
    _ENVS[env_id] = Env(
        env_id=env_id,
        problem=problem,
        mem0=mem.copy(),
        program=builder.instrs,
        debug_info=debug_info,
        machine=machine,
        forest_height=forest_height,
        batch_size=batch_size,
        rounds=rounds,
        seed=seed,
        enable_debug=enable_debug,
        trace=trace,
    )

    return {
        "env_id": env_id,
        "mem_size": len(mem),
        "program_len": len(builder.instrs),
        "scratch_size": problem.SCRATCH_SIZE,
    }


def reset_env(env_id: int) -> dict[str, Any]:
    """
    Reset machine state and memory back to the initial image.

    Args:
        env_id: Environment id to reset.
    """
    env = _require_env(env_id)
    problem = env.problem
    value_trace = _build_value_trace(problem, env.mem0) if env.enable_debug else {}

    machine = problem.Machine(
        env.mem0.copy(),
        env.program,
        env.debug_info,
        n_cores=problem.N_CORES,
        scratch_size=problem.SCRATCH_SIZE,
        trace=env.trace,
        value_trace=value_trace,
    )
    if not env.enable_debug:
        machine.enable_debug = False

    env.machine = machine
    return {"env_id": env_id, "cycle": env.machine.cycle}


def run(env_id: int, max_cycles: int | None = None, max_instructions: int | None = None) -> dict[str, Any]:
    """
    Run the machine until halt (or a max cycle/instruction limit).

    Args:
        env_id: Environment id to run.
        max_cycles: Optional maximum cycle count.
        max_instructions: Optional maximum instruction bundles to execute.
    """
    env = _require_env(env_id)
    steps = _run_machine(env.machine, max_cycles, max_instructions)
    return {
        "env_id": env_id,
        "cycle": env.machine.cycle,
        "steps": steps,
        "pcs": [c.pc for c in env.machine.cores],
        "states": [c.state.name for c in env.machine.cores],
        "halted": all(c.state == c.state.STOPPED for c in env.machine.cores),
    }


def step(env_id: int, n: int = 1) -> dict[str, Any]:
    """
    Execute n instruction bundles.

    Args:
        env_id: Environment id to step.
        n: Number of instruction bundles to execute.
    """
    env = _require_env(env_id)
    steps = _run_machine(env.machine, None, n)
    return {
        "env_id": env_id,
        "cycle": env.machine.cycle,
        "steps": steps,
        "pcs": [c.pc for c in env.machine.cores],
        "states": [c.state.name for c in env.machine.cores],
    }


def read_mem(env_id: int, start: int, length: int) -> dict[str, Any]:
    """
    Read a contiguous range of memory.

    Args:
        env_id: Environment id to read from.
        start: Start address.
        length: Number of words to read.
    """
    env = _require_env(env_id)
    end = max(start, min(len(env.machine.mem), start + length))
    return {"env_id": env_id, "start": start, "end": end, "values": env.machine.mem[start:end]}


def read_scratch(env_id: int, addrs: list[int], core_id: int = 0) -> dict[str, Any]:
    """
    Read scratch addresses from a core.

    Args:
        env_id: Environment id to read from.
        addrs: Scratch addresses to read.
        core_id: Core id (default 0).
    """
    env = _require_env(env_id)
    if core_id < 0 or core_id >= len(env.machine.cores):
        raise ValueError(f"invalid core_id {core_id}")
    core = env.machine.cores[core_id]
    values = {addr: core.scratch[addr] for addr in addrs}
    return {"env_id": env_id, "core_id": core_id, "values": values}


def validate_program(program_json: str) -> dict[str, Any]:
    """
    Validate a program JSON string against slot limits.

    Args:
        program_json: JSON-encoded list of instruction dicts.
    """
    problem = _load_problem(use_frozen=False)
    try:
        program = json.loads(program_json)
    except json.JSONDecodeError as exc:
        return {"ok": False, "errors": [f"json: {exc}"]}

    errors: list[str] = []
    if not isinstance(program, list):
        return {"ok": False, "errors": ["program must be a list of instruction dicts"]}

    for i, instr in enumerate(program):
        if not isinstance(instr, dict):
            errors.append(f"instr {i}: not a dict")
            continue
        for engine, slots in instr.items():
            if engine not in problem.SLOT_LIMITS:
                errors.append(f"instr {i}: unknown engine '{engine}'")
                continue
            if not isinstance(slots, list):
                errors.append(f"instr {i}: engine '{engine}' slots must be a list")
                continue
            if len(slots) > problem.SLOT_LIMITS[engine]:
                errors.append(
                    f"instr {i}: engine '{engine}' has {len(slots)} slots, limit {problem.SLOT_LIMITS[engine]}"
                )

    return {"ok": len(errors) == 0, "errors": errors}


def set_program(env_id: int, program_json: str) -> dict[str, Any]:
    """
    Replace the machine program with a JSON-encoded list of instructions.

    Args:
        env_id: Environment id to update.
        program_json: JSON-encoded list of instruction dicts.
    """
    env = _require_env(env_id)
    result = validate_program(program_json)
    if not result["ok"]:
        return result

    program = json.loads(program_json)
    env.program = program
    env.machine.program = program
    return {"ok": True, "env_id": env_id, "program_len": len(program)}


TOOL_FUNCS = [
    get_limits,
    list_variants,
    sweep_caps,
    run_variant,
    compare_variants,
    make_env,
    reset_env,
    run,
    step,
    read_mem,
    read_scratch,
    validate_program,
    set_program,
]
