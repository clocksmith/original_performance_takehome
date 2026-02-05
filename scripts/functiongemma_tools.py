from __future__ import annotations

import json
import random
import sys
from dataclasses import dataclass, fields
from importlib import util
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from perf_takehome import KernelBuilder

from generator.op_list import build_ops
from generator.ops import Op
from generator.schedule_dep import _reads_writes, schedule_ops_dep
from generator.scratch_layout import ScratchAlloc, build_layout
from kernel_analyzer import analyze_instrs
from problem import DebugInfo, SLOT_LIMITS, VLEN


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
    "cache_top4_d4x15_reset_offload_1013": ROOT / "wrappers" / "_autogen_cache" / "cache_top4_d4x15_reset_offload_1013.py",
    "cache_top4_d4x15_reset_offload_1015_full_window": ROOT / "wrappers" / "_autogen_cache" / "cache_top4_d4x15_reset_offload_1015_full_window.py",
    "cache_top4_d4x15_reset_offload_1016": ROOT / "wrappers" / "_autogen_cache" / "cache_top4_d4x15_reset_offload_1016.py",
    "loadbound_preload15_uncached_1316": ROOT / "loadbound_preload15_uncached_1316.py",
}

_BASE_SPEC_PROFILES: dict[str, str] = {
    "base": "base",
    "default": "base",
    "offload_base": "offload",
    "offload": "offload",
    "1013": "offload",
    "full_isa_base": "full_isa",
    "full_isa": "full_isa",
    "1016": "full_isa",
}


def _normalize_base_spec(name: str) -> str | None:
    return _BASE_SPEC_PROFILES.get(name)


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


def _load_generator_module(name: str):
    # Prefer package import so relative imports inside generator modules work.
    try:
        return importlib.import_module(f"generator.{name}")
    except Exception:
        pass
    gen_path = ROOT / "generator" / f"{name}.py"
    if not gen_path.exists():
        return None
    module_name = f"generator_{name}"
    spec = util.spec_from_file_location(module_name, str(gen_path))
    if spec is None or spec.loader is None:
        raise ImportError(f"Failed to load generator module: {gen_path}")
    module = util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _validate_variant_name(name: str) -> None:
    if not name or not all(c.isalnum() or c == "_" for c in name):
        raise ValueError("variant name must be alphanumeric/underscore only")


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


def _isa_op_counts() -> dict[str, dict[str, int]]:
    alu_ops = ["+", "-", "*", "//", "cdiv", "^", "&", "|", "<<", ">>", "%", "<", "=="]
    op_counts: dict[str, dict[str, int]] = {
        "alu": {op: 3 for op in alu_ops},
        "valu": {op: 3 for op in alu_ops},
        "load": {
            "load": 2,
            "load_offset": 3,
            "vload": 2,
            "const": 2,
        },
        "store": {"store": 2, "vstore": 2},
        "flow": {
            "select": 4,
            "add_imm": 3,
            "vselect": 4,
            "halt": 0,
            "pause": 0,
            "trace_write": 1,
            "cond_jump": 2,
            "cond_jump_rel": 2,
            "jump": 1,
            "jump_indirect": 1,
            "coreid": 1,
        },
        "debug": {"compare": 2, "vcompare": 2},
    }
    op_counts["valu"].update({"vbroadcast": 2, "multiply_add": 4})
    return op_counts


def _validate_instruction_obj(
    instr: dict[str, list[list[Any]]], use_frozen: bool, validate_ops: bool
) -> list[str]:
    errors: list[str] = []
    problem = _load_problem(use_frozen)
    slot_limits = problem.SLOT_LIMITS
    op_counts = _isa_op_counts() if validate_ops else {}

    if not isinstance(instr, dict):
        return ["instruction must be a dict"]

    for engine, slots in instr.items():
        if engine not in slot_limits:
            errors.append(f"unknown engine '{engine}'")
            continue
        if not isinstance(slots, list):
            errors.append(f"engine '{engine}' slots must be a list")
            continue
        if len(slots) > slot_limits[engine]:
            errors.append(
                f"engine '{engine}' has {len(slots)} slots, limit {slot_limits[engine]}"
            )
        if not validate_ops:
            continue
        engine_ops = op_counts.get(engine, {})
        for si, slot in enumerate(slots):
            if not isinstance(slot, (list, tuple)) or len(slot) == 0:
                errors.append(f"engine '{engine}' slot {si} must be a non-empty list")
                continue
            op = slot[0]
            if op not in engine_ops:
                errors.append(f"engine '{engine}' slot {si} has unknown op '{op}'")
                continue
            expected = engine_ops[op]
            got = len(slot) - 1
            if got != expected:
                errors.append(
                    f"engine '{engine}' slot {si} op '{op}' expects {expected} args, got {got}"
                )

    return errors


def get_isa_spec(use_frozen: bool = True) -> dict[str, Any]:
    """
    Return ISA slot limits and op signatures.

    Args:
        use_frozen: If True, use tests/frozen_problem semantics.
    """
    problem = _load_problem(use_frozen)
    return {
        "slot_limits": problem.SLOT_LIMITS,
        "vlen": problem.VLEN,
        "n_cores": problem.N_CORES,
        "scratch_size": problem.SCRATCH_SIZE,
        "op_arg_counts": _isa_op_counts(),
    }


def assemble_instruction(
    slots: dict[str, list[list[Any]]],
    validate: bool = True,
    use_frozen: bool = True,
) -> dict[str, Any]:
    """
    Assemble a single instruction bundle from engine slots.

    Args:
        slots: Mapping of engine -> list of slot lists.
        validate: If True, validate slot limits and op arity.
        use_frozen: If True, use tests/frozen_problem semantics.
    """
    instr = slots
    errors: list[str] = []
    if validate:
        errors = _validate_instruction_obj(instr, use_frozen, validate_ops=True)
    return {"ok": len(errors) == 0, "instruction": instr, "errors": errors}


def assemble_program(
    instructions: list[dict[str, list[list[Any]]]],
    validate: bool = True,
    use_frozen: bool = True,
) -> dict[str, Any]:
    """
    Assemble a program (list of instruction bundles).

    Args:
        instructions: List of instruction dicts.
        validate: If True, validate slot limits and op arity.
        use_frozen: If True, use tests/frozen_problem semantics.
    """
    errors: list[str] = []
    if not isinstance(instructions, list):
        return {"ok": False, "errors": ["instructions must be a list"], "program": []}

    if validate:
        for i, instr in enumerate(instructions):
            if not isinstance(instr, dict):
                errors.append(f"instr {i}: not a dict")
                continue
            instr_errors = _validate_instruction_obj(instr, use_frozen, validate_ops=True)
            errors.extend([f"instr {i}: {e}" for e in instr_errors])

    program_json = json.dumps(instructions)
    return {
        "ok": len(errors) == 0,
        "program": instructions,
        "program_json": program_json,
        "errors": errors,
    }


def validate_program_ops(program_json: str, use_frozen: bool = True) -> dict[str, Any]:
    """
    Validate a program JSON string against slot limits and op signatures.

    Args:
        program_json: JSON-encoded list of instruction dicts.
        use_frozen: If True, use tests/frozen_problem semantics.
    """
    try:
        program = json.loads(program_json)
    except json.JSONDecodeError as exc:
        return {"ok": False, "errors": [f"json: {exc}"]}

    if not isinstance(program, list):
        return {"ok": False, "errors": ["program must be a list of instruction dicts"]}

    errors: list[str] = []
    for i, instr in enumerate(program):
        if not isinstance(instr, dict):
            errors.append(f"instr {i}: not a dict")
            continue
        instr_errors = _validate_instruction_obj(instr, use_frozen, validate_ops=True)
        errors.extend([f"instr {i}: {e}" for e in instr_errors])

    return {"ok": len(errors) == 0, "errors": errors}


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


_OP_GRAPH_STRATEGIES: dict[str, dict[str, Any]] = {
    "mask_precompute_idxshift": {
        "base_spec": "offload",
        "description": "Mask-precompute selection with idx-shifted vectors and extra scratch.",
        "overrides": {
            "selection_mode": "mask_precompute",
            "idx_shifted": True,
            "extra_vecs": 4,
            "vector_block": 4,
            "include_setup": False,
        },
    },
    "mask_idxshift": {
        "base_spec": "offload",
        "description": "Mask selection with idx-shifted vectors and extra scratch.",
        "overrides": {
            "selection_mode": "mask",
            "idx_shifted": True,
            "extra_vecs": 4,
            "vector_block": 4,
            "include_setup": False,
        },
    },
    "bitmask_idxshift": {
        "base_spec": "full_isa",
        "description": "Bitmask selection with idx-shifted vectors and no depth4 caching.",
        "overrides": {
            "use_bitmask_selection": True,
            "selection_mode": "bitmask",
            "idx_shifted": True,
            "depth4_rounds": 0,
            "depth4_cached_rounds": (),
            "x4": 0,
        },
    },
    "bitmask_idxshift_resetflow": {
        "base_spec": "full_isa",
        "description": "Bitmask selection + idx shift with reset on flow (no depth4 caching).",
        "overrides": {
            "use_bitmask_selection": True,
            "selection_mode": "bitmask",
            "idx_shifted": True,
            "reset_on_valu": False,
            "depth4_rounds": 0,
            "depth4_cached_rounds": (),
            "x4": 0,
        },
    },
    "top3_loadbound_ptralu": {
        "base_spec": "offload",
        "description": "Top-3 caching, idx-shifted, pointer setup on ALU.",
        "overrides": {
            "cached_nodes": 7,
            "base_cached_rounds": (0, 1, 2, 11, 12, 13),
            "depth4_rounds": 0,
            "x4": 0,
            "idx_shifted": True,
            "ptr_setup_engine": "alu",
            "include_setup": False,
        },
    },
    "skip_r3_x4_24_parity_off": {
        "base_spec": "full_isa",
        "description": "Skip round 3 caching, X4=24, parity offload.",
        "overrides": {
            "base_cached_rounds": (0, 1, 2, 11, 12, 13, 14),
            "depth4_rounds": 1,
            "depth4_cached_rounds": (4,),
            "x4": 24,
            "cached_nodes": 31,
            "idx_shifted": True,
            "offload_hash_op1": False,
            "offload_parity": True,
            "offload_op1": 448,
        },
    },
}


def list_op_graph_strategies() -> dict[str, Any]:
    """
    List op-graph strategy templates for create_op_graph_variant().
    """
    strategies = []
    for name, cfg in _OP_GRAPH_STRATEGIES.items():
        strategies.append(
            {
                "name": name,
                "base_spec": cfg["base_spec"],
                "description": cfg.get("description", ""),
                "overrides": cfg.get("overrides", {}),
            }
        )
    return {"strategies": strategies}


def create_op_graph_variant(
    name: str,
    strategy: str,
    base_spec: str | None = None,
    overrides: dict[str, Any] | None = None,
    register: bool = True,
    overwrite: bool = False,
    create_proof: bool = True,
) -> dict[str, Any]:
    """
    Create a variant using a predefined op-graph strategy template.

    Args:
        name: Variant name (alphanumeric + underscore).
        strategy: Strategy key from list_op_graph_strategies().
        base_spec: Optional override for base spec ("base", "offload", or "full_isa").
        overrides: Extra spec overrides to merge on top of the template.
        register: If True, add to in-memory variant registry.
        overwrite: If True, overwrite existing files.
        create_proof: If True, create proof stubs and update proof_map.json.
    """
    if strategy not in _OP_GRAPH_STRATEGIES:
        return {"ok": False, "error": f"unknown op-graph strategy '{strategy}'"}
    template = _OP_GRAPH_STRATEGIES[strategy]
    base = base_spec or template["base_spec"]
    merged = dict(template.get("overrides", {}))
    if overrides:
        merged.update(overrides)
    return create_variant(
        name=name,
        base_spec=base,
        overrides=merged,
        register=register,
        overwrite=overwrite,
        create_proof=create_proof,
    )


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


def sweep_proof_strategies(
    config_path: str | None = None,
    strategy: str | None = None,
    T_values: list[int] | None = None,
    max_results_per_strategy: int | None = None,
) -> dict[str, Any]:
    """
    Sweep proof strategies defined in scripts/proof_strategies.json.

    Args:
        config_path: Optional path to a proof strategies JSON file.
        strategy: Optional strategy name to filter.
        T_values: Optional override of cycle budgets for all strategies.
        max_results_per_strategy: Optional cap on results per strategy.
    """
    from scripts.sweep_caps import feasible_strategy, format_rows

    if config_path is None:
        config_path = str(ROOT / "scripts" / "proof_strategies.json")
    cfg_path = Path(config_path)
    if not cfg_path.exists():
        return {"ok": False, "error": f"config not found: {config_path}"}

    data = json.loads(cfg_path.read_text(encoding="utf-8"))
    strategies = data.get("strategies", [])
    if strategy:
        strategies = [cfg for cfg in strategies if cfg.get("name") == strategy]
        if not strategies:
            return {"ok": False, "error": f"strategy not found: {strategy}"}

    results = []
    for cfg in strategies:
        name = cfg.get("name", "<unknown>")
        if T_values is not None:
            Ts = list(T_values)
        else:
            T_cfg = cfg.get("T")
            if isinstance(T_cfg, list):
                Ts = [int(v) for v in T_cfg]
            elif T_cfg is None:
                Ts = [1013, 1016]
            else:
                Ts = [int(T_cfg)]
        res = feasible_strategy(cfg, T_values=Ts)
        if max_results_per_strategy is not None:
            res = res[:max_results_per_strategy]
        results.append(
            {
                "strategy": name,
                "T_values": Ts,
                "results": [r.__dict__ for r in res],
                "summary": format_rows(res) if res else [],
            }
        )

    return {"ok": True, "config_path": str(cfg_path), "strategies": results}


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


def create_variant(
    name: str,
    base_spec: str = "offload",
    overrides: dict[str, Any] | None = None,
    register: bool = True,
    overwrite: bool = False,
    create_proof: bool = True,
    alias_of: str | None = None,
) -> dict[str, Any]:
    """
    Create a generator spec override + kernel wrapper and optionally register it.

    Args:
        name: Variant name (alphanumeric + underscore).
        base_spec: "base", "offload", or "full_isa" (legacy 1013/1016 accepted).
        overrides: Spec override dict (e.g. {"offload_op1": 826}).
        register: If True, add to the in-memory variant registry.
        overwrite: If True, overwrite existing files.
        create_proof: If True, create proof stubs and update proof_map.json.
        alias_of: Optional proof_name this spec aliases (proof mapping only).
    """
    _validate_variant_name(name)
    overrides = overrides or {}

    base_spec_norm = _normalize_base_spec(base_spec)
    if base_spec_norm is None:
        return {
            "ok": False,
            "error": (
                f"unknown base_spec '{base_spec}' (use base/offload/full_isa; "
                "legacy 1013/1016 accepted)"
            ),
        }

    gen_path = ROOT / "generator" / f"{name}.py"
    wrapper_path = ROOT / f"{name}.py"
    proof_dir = ROOT / "proofs" / name
    proof_md = proof_dir / "LowerBound.md"
    proof_lean = proof_dir / "LowerBound.lean"
    proof_map_path = ROOT / "scripts" / "proof_map.json"

    if not overwrite:
        if name in _VARIANTS:
            return {"ok": False, "error": f"variant '{name}' already registered"}
        if gen_path.exists() or wrapper_path.exists():
            return {"ok": False, "error": f"variant files already exist for '{name}'"}
        if create_proof and proof_dir.exists():
            return {"ok": False, "error": f"proof directory already exists for '{name}'"}

    from generator.spec_base import SPEC_BASE, OFFLOAD_DEFAULTS
    from generator.build_kernel_base import build_base_instrs

    spec_obj = SPEC_BASE
    spec_import = "from generator.spec_base import SPEC_BASE"
    build_import = "from generator.build_kernel_base import build_base_instrs"
    build_call = "build_base_instrs"

    profile_overrides: dict[str, Any] = {}
    if base_spec_norm == "offload":
        profile_overrides = dict(OFFLOAD_DEFAULTS)

    field_names = {f.name for f in fields(type(spec_obj))}
    bad_keys = [k for k in overrides.keys() if k not in field_names]
    if bad_keys:
        return {"ok": False, "error": f"unknown spec fields: {bad_keys}"}

    tuple_fields = {f.name for f in fields(type(spec_obj)) if str(f.type).startswith("tuple")}
    clean_overrides: dict[str, Any] = {}
    for key, value in overrides.items():
        if key in tuple_fields and isinstance(value, list):
            clean_overrides[key] = tuple(value)
        else:
            clean_overrides[key] = value

    merged_overrides = {**profile_overrides, **clean_overrides}

    spec_const = f"SPEC_{name.upper()}"
    if merged_overrides:
        override_lines = ",\n    ".join(f"{k}={repr(v)}" for k, v in merged_overrides.items())
        spec_def = (
            f"{spec_const} = replace(\n"
            f"    {spec_import.split()[-1]},\n"
            f"    {override_lines},\n"
            ")\n"
        )
        spec_ref = spec_const
    else:
        spec_def = f"{spec_const} = {spec_import.split()[-1]}\n"
        spec_ref = spec_const

    gen_code = (
        "from __future__ import annotations\n\n"
        "from dataclasses import replace\n\n"
        f"{spec_import}\n"
        f"{build_import}\n\n"
        f"{spec_def}\n"
        "def build_instrs():\n"
        f"    return {build_call}(spec={spec_ref})\n"
    )

    wrapper_code = (
        "from perf_takehome import KernelBuilder as BaseKernelBuilder\n"
        f"from generator.{name} import build_instrs\n\n\n"
        "class KernelBuilder(BaseKernelBuilder):\n"
        "    def build_kernel(\n"
        "        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int\n"
        "    ):\n"
        "        self.instrs = build_instrs()\n"
    )

    gen_path.write_text(gen_code, encoding="utf-8")
    wrapper_path.write_text(wrapper_code, encoding="utf-8")

    proof_created = False
    proof_map_updated = False
    if create_proof:
        proof_dir.mkdir(parents=True, exist_ok=True)
        if not proof_md.exists():
            proof_md.write_text(
                (
                    f"# {name}\n\n"
                    "TODO: Fill in capacity bounds and assumptions.\n"
                ),
                encoding="utf-8",
            )
        if not proof_lean.exists():
            proof_lean.write_text(
                (
                    "import proofs.common.ISA\n"
                    "import proofs.common.Machine\n\n"
                    f"-- Proof stub for {name}\n"
                    "-- TODO: add lower-bound lemmas and capacity proofs.\n"
                ),
                encoding="utf-8",
            )
        proof_created = True

        # Update proof_map.json
        spec_entry = {
            "module": f"generator.{name}",
            "object": spec_const,
        }
        if alias_of:
            spec_entry["alias_of"] = alias_of
        mapping = {
            "proof_name": name,
            "spec": spec_entry,
            "generator": {
                "module": f"generator.{name}",
                "function": "build_instrs",
            },
            "kernel_wrapper": {
                "path": f"{name}.py",
                "class": "KernelBuilder",
            },
        }

        if proof_map_path.exists():
            data = json.loads(proof_map_path.read_text(encoding="utf-8"))
        else:
            data = {"version": 1, "mappings": []}
        mappings = data.get("mappings", [])
        idx = next((i for i, m in enumerate(mappings) if m.get("proof_name") == name), None)
        if idx is not None:
            if not overwrite:
                return {"ok": False, "error": f"proof_map already contains '{name}'"}
            mappings[idx] = mapping
        else:
            mappings.append(mapping)
        data["mappings"] = mappings
        proof_map_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        proof_map_updated = True

    if register:
        _VARIANTS[name] = wrapper_path

    return {
        "ok": True,
        "name": name,
        "base_spec": base_spec_norm,
        "generator_path": str(gen_path),
        "wrapper_path": str(wrapper_path),
        "proof_dir": str(proof_dir) if create_proof else None,
        "proof_created": proof_created,
        "proof_map_updated": proof_map_updated,
        "registered": register,
    }


def _build_setup_instrs_1013(spec, layout) -> list[dict[str, list[tuple[Any, ...]]]]:
    setup_instrs: list[dict[str, list[tuple[Any, ...]]]] = []

    def _pack(engine: str, slots: list[tuple[Any, ...]]) -> None:
        cap = SLOT_LIMITS[engine]
        for i in range(0, len(slots), cap):
            setup_instrs.append({engine: slots[i : i + cap]})

    const_loads = [("const", addr, val) for val, addr in sorted(layout.const_s.items())]
    _pack("load", const_loads)

    ptr_loads = [
        ("load", layout.forest_values_p, layout.const_s[4]),
        ("load", layout.inp_indices_p, layout.const_s[5]),
        ("load", layout.inp_values_p, layout.const_s[6]),
    ]
    _pack("load", ptr_loads)

    flow_setup = [
        ("add_imm", layout.idx_ptr[0], layout.inp_indices_p, 0),
        ("add_imm", layout.val_ptr[0], layout.inp_values_p, 0),
    ]
    for v in range(1, spec.vectors):
        flow_setup.append(("add_imm", layout.idx_ptr[v], layout.idx_ptr[v - 1], VLEN))
        flow_setup.append(("add_imm", layout.val_ptr[v], layout.val_ptr[v - 1], VLEN))
    _pack("flow", flow_setup)

    for i, vaddr in enumerate(layout.node_v):
        setup_instrs.append({"alu": [("+", layout.node_tmp, layout.forest_values_p, layout.const_s[i])]})
        setup_instrs.append({"load": [("load", layout.node_tmp, layout.node_tmp)]})
        setup_instrs.append({"valu": [("vbroadcast", vaddr, layout.node_tmp)]})

    const_v_broadcasts = [
        ("vbroadcast", vaddr, layout.const_s[val]) for val, vaddr in sorted(layout.const_v.items())
    ]
    _pack("valu", const_v_broadcasts)

    vloads = []
    for v in range(spec.vectors):
        vloads.append(("vload", layout.idx[v], layout.idx_ptr[v]))
        vloads.append(("vload", layout.val[v], layout.val_ptr[v]))
    _pack("load", vloads)

    return setup_instrs


def _build_final_ops(spec, layout) -> list[Op]:
    ordered_ops: list[Op] = []
    build_ops(spec, layout, ordered_ops=ordered_ops)

    final_ops: list[Op] = []
    offloaded = 0
    offload_limit = getattr(spec, "offload_op1", 0)
    for op in ordered_ops:
        if op.offloadable and offloaded < offload_limit:
            op_name, dest, a, b = op.slot
            for lane in range(VLEN):
                final_ops.append(
                    Op(
                        engine="alu",
                        slot=(op_name, dest + lane, a + lane, b + lane),
                        meta=op.meta,
                    )
                )
            offloaded += 1
        else:
            final_ops.append(op)

    pad_cycles = getattr(spec, "valu_pad_cycles", 0)
    if pad_cycles:
        pad_count = pad_cycles * getattr(spec, "valu_cap", 0)
        pad_dest = layout.tmp[0]
        for _ in range(pad_count):
            final_ops.insert(0, Op(engine="valu", slot=("^", pad_dest, pad_dest, pad_dest)))

    return final_ops


def _resolve_schedule_target(name: str) -> tuple[str, Any, Any]:
    base_spec_norm = _normalize_base_spec(name)
    if base_spec_norm in {"base", "full_isa"}:
        from generator.spec_base import SPEC_BASE
        from generator.build_kernel_base import build_base_instrs

        return base_spec_norm, SPEC_BASE, build_base_instrs

    if base_spec_norm == "offload":
        from generator.spec_base import with_offload_defaults
        from generator.build_kernel_base import build_base_instrs

        spec_obj = with_offload_defaults()

        def _build() -> list[dict[str, list[tuple]]]:
            return build_base_instrs(spec=spec_obj)

        return "offload", spec_obj, _build

    if name == "cache_top4_d4x15_reset_offload_1013":
        from generator.cache_top4_d4x15_reset_offload_1013 import SPEC_PROOF_1013, build_instrs

        return name, SPEC_PROOF_1013, build_instrs

    if name == "cache_top4_d4x15_reset_offload_1015_full_window":
        from generator.cache_top4_d4x15_reset_offload_1015_full_window import build_instrs
        from generator.cache_top4_d4x15_reset_offload_1013 import SPEC_PROOF_1013

        return name, SPEC_PROOF_1013, build_instrs

    if name == "cache_top4_d4x15_reset_offload_1016":
        from generator.cache_top4_d4x15_reset_offload_1016 import build_instrs
        from generator.spec_base import SPEC_BASE

        return name, SPEC_BASE, build_instrs

    if name == "loadbound_preload15_uncached_1316":
        from generator.loadbound_preload15_uncached_1316 import SPEC_LOADBOUND_1316, build_instrs

        return name, SPEC_LOADBOUND_1316, build_instrs

    module = _load_generator_module(name)
    if module is not None:
        spec_obj = None
        preferred = f"SPEC_{name.upper()}"
        if hasattr(module, preferred):
            spec_obj = getattr(module, preferred)
        else:
            for attr in dir(module):
                if attr.startswith("SPEC_"):
                    spec_obj = getattr(module, attr)
                    break
        build_fn = getattr(module, "build_instrs", None)
        if build_fn is None:
            raise ValueError(f"Generator module '{name}' lacks build_instrs().")
        return name, spec_obj, build_fn

    raise ValueError(
        f"Unknown spec '{name}' (expected proof/variant name or base/offload/full_isa)."
    )


def schedule_summary(spec: str = "cache_top4_d4x15_reset_offload_1013") -> dict[str, Any]:
    """
    Build generator schedule and return cycle utilization stats.

    Args:
        spec: Proof/variant name (e.g. cache_top4_d4x15_reset_offload_1013) or "base"/\"offload\"/\"full_isa\".
    """
    display, spec_obj, build_fn = _resolve_schedule_target(spec)
    instrs = build_fn()

    report = analyze_instrs(instrs)
    stats = {
        eng: {
            "total_slots": st.total_slots,
            "max_per_cycle": st.max_per_cycle,
            "op_counts": dict(st.op_counts) if st.op_counts else {},
        }
        for eng, st in report["stats"].items()
    }
    return {
        "spec": display,
        "resolved_spec": type(spec_obj).__name__ if spec_obj is not None else None,
        "cycles": report["cycles"],
        "caps": report["caps"],
        "utilization": report["utilization"],
        "stats": stats,
    }


def find_schedule_mismatch(
    spec: str = "cache_top4_d4x15_reset_offload_1013",
    forest_height: int = 10,
    rounds: int = 16,
    batch_size: int = 256,
    seed: int | None = 0,
    use_frozen: bool = True,
    max_ops: int | None = None,
) -> dict[str, Any]:
    """
    Compare sequential op order vs dependency schedule, return first mismatch.

    Args:
        spec: Proof/variant name (e.g. cache_top4_d4x15_reset_offload_1016) or "base"/\"offload\"/\"full_isa\".
        forest_height: Tree height.
        rounds: Number of rounds.
        batch_size: Number of inputs.
        seed: RNG seed for deterministic inputs (None for random).
        use_frozen: If True, use tests/frozen_problem semantics.
        max_ops: Optional cap on op count to check.
    """
    if seed is not None:
        random.seed(seed)

    problem = _load_problem(use_frozen)
    forest = problem.Tree.generate(forest_height)
    inp = problem.Input.generate(forest, batch_size, rounds)
    mem = problem.build_mem_image(forest, inp)

    display, spec_obj, _ = _resolve_schedule_target(spec)
    if spec_obj is None:
        return {"ok": False, "spec": display, "error": "spec object not found for mismatch analysis"}

    scratch = ScratchAlloc()
    layout = build_layout(spec_obj, scratch)

    setup_style = getattr(spec_obj, "setup_style", "inline")
    setup_instrs = _build_setup_instrs_1013(spec_obj, layout) if setup_style == "packed" else []

    final_ops = _build_final_ops(spec_obj, layout)
    if max_ops is not None:
        final_ops = final_ops[:max_ops]

    debug_info = DebugInfo(scratch_map={})

    # Run setup to seed scratch/mem state.
    setup_machine = problem.Machine(
        mem.copy(),
        [],
        debug_info,
        n_cores=problem.N_CORES,
        scratch_size=problem.SCRATCH_SIZE,
    )
    setup_core = setup_machine.cores[0]
    for instr in setup_instrs:
        setup_machine.step(instr, setup_core)

    scratch0 = setup_core.scratch.copy()
    mem0 = setup_machine.mem.copy()

    # Sequential expected reads.
    seq_machine = problem.Machine(
        mem0.copy(),
        [],
        debug_info,
        n_cores=problem.N_CORES,
        scratch_size=problem.SCRATCH_SIZE,
    )
    seq_core = seq_machine.cores[0]
    seq_core.scratch = scratch0.copy()

    seq_reads: list[dict[int, int]] = []
    for op in final_ops:
        reads, _ = _reads_writes(op)
        seq_reads.append({addr: seq_core.scratch[addr] for addr in reads})
        seq_machine.step({op.engine: [op.slot]}, seq_core)

    op_index = {id(op): i for i, op in enumerate(final_ops)}
    instrs_ops = schedule_ops_dep(final_ops, return_ops=True)

    sched_machine = problem.Machine(
        mem0.copy(),
        [],
        debug_info,
        n_cores=problem.N_CORES,
        scratch_size=problem.SCRATCH_SIZE,
    )
    sched_core = sched_machine.cores[0]
    sched_core.scratch = scratch0.copy()

    for cycle, instr in enumerate(instrs_ops):
        for engine, ops in instr.items():
            for op in ops:
                idx = op_index[id(op)]
                expected = seq_reads[idx]
                for addr, exp in expected.items():
                    actual = sched_core.scratch[addr]
                    if actual != exp:
                        return {
                            "ok": False,
                            "spec": display,
                            "resolved_spec": type(spec_obj).__name__ if spec_obj is not None else None,
                            "op_index": idx,
                            "cycle": cycle,
                            "engine": engine,
                            "slot": op.slot,
                            "addr": addr,
                            "expected": exp,
                            "actual": actual,
                            "meta": op.meta or {},
                        }

        instr_slots = {eng: [op.slot for op in ops] for eng, ops in instr.items()}
        sched_machine.step(instr_slots, sched_core)

    return {
        "ok": True,
        "spec": display,
        "resolved_spec": type(spec_obj).__name__ if spec_obj is not None else None,
        "ops": len(final_ops),
        "cycles": len(instrs_ops),
    }


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


def run_program(
    program_json: str,
    forest_height: int = 3,
    rounds: int = 1,
    batch_size: int = 8,
    seed: int | None = 0,
    use_frozen: bool = True,
    max_cycles: int | None = None,
    max_instructions: int | None = None,
    enable_debug: bool = False,
    mem_size: int | None = None,
) -> dict[str, Any]:
    """
    Run a JSON program on a fresh Machine instance.

    Args:
        program_json: JSON-encoded list of instruction dicts.
        forest_height: Tree height (ignored if mem_size is provided).
        rounds: Number of rounds (ignored if mem_size is provided).
        batch_size: Number of inputs (ignored if mem_size is provided).
        seed: RNG seed for deterministic inputs (None for random).
        use_frozen: If True, use tests/frozen_problem semantics.
        max_cycles: Optional maximum cycle count.
        max_instructions: Optional maximum instruction bundles to execute.
        enable_debug: If True, enable debug compare slots (requires valid trace keys).
        mem_size: If provided, use a zeroed memory image of this size.
    """
    try:
        program = json.loads(program_json)
    except json.JSONDecodeError as exc:
        return {"ok": False, "errors": [f"json: {exc}"]}

    if not isinstance(program, list):
        return {"ok": False, "errors": ["program must be a list of instruction dicts"]}

    errors: list[str] = []
    for i, instr in enumerate(program):
        if not isinstance(instr, dict):
            errors.append(f"instr {i}: not a dict")
            continue
        instr_errors = _validate_instruction_obj(instr, use_frozen, validate_ops=True)
        errors.extend([f"instr {i}: {e}" for e in instr_errors])
    if errors:
        return {"ok": False, "errors": errors}

    if seed is not None:
        random.seed(seed)

    problem = _load_problem(use_frozen)
    if mem_size is not None:
        mem = [0] * mem_size
    else:
        forest = problem.Tree.generate(forest_height)
        inp = problem.Input.generate(forest, batch_size, rounds)
        mem = problem.build_mem_image(forest, inp)

    value_trace = _build_value_trace(problem, mem) if enable_debug else {}
    debug_info = problem.DebugInfo(scratch_map={})
    machine = problem.Machine(
        mem,
        program,
        debug_info,
        n_cores=problem.N_CORES,
        scratch_size=problem.SCRATCH_SIZE,
        trace=False,
        value_trace=value_trace,
    )
    if not enable_debug:
        machine.enable_debug = False

    steps = _run_machine(machine, max_cycles, max_instructions)
    return {
        "ok": True,
        "cycle": machine.cycle,
        "steps": steps,
        "pcs": [c.pc for c in machine.cores],
        "states": [c.state.name for c in machine.cores],
        "halted": all(c.state == c.state.STOPPED for c in machine.cores),
        "mem_size": len(machine.mem),
    }


TOOL_FUNCS = [
    get_limits,
    get_isa_spec,
    list_variants,
    list_op_graph_strategies,
    sweep_caps,
    sweep_proof_strategies,
    run_variant,
    compare_variants,
    create_variant,
    create_op_graph_variant,
    schedule_summary,
    find_schedule_mismatch,
    assemble_instruction,
    assemble_program,
    make_env,
    reset_env,
    run,
    step,
    read_mem,
    read_scratch,
    validate_program,
    validate_program_ops,
    set_program,
    run_program,
]
