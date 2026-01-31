from __future__ import annotations

import argparse
import json
import os
import random
from pathlib import Path
from typing import Any

import torch
from datasets import Dataset
from peft import LoraConfig, get_peft_model
from transformers import AutoModelForCausalLM, AutoProcessor, AutoTokenizer
from transformers.utils import get_json_schema
from trl import SFTConfig, SFTTrainer

from functiongemma_tools import TOOL_FUNCS

DEFAULT_SYSTEM_MSG = "You are a model that can do function calling with the following functions"


def resolve_model_path(model_path: str | None) -> str:
    if model_path:
        return model_path
    local_copy = Path(__file__).resolve().parent.parent / "models" / "functiongemma-270m-it"
    if local_copy.exists():
        return str(local_copy)
    env_override = os.getenv("FUNCTIONGEMMA_PATH")
    if env_override:
        return env_override
    default_cache = os.path.expanduser(
        "~/.cache/huggingface/hub/models--google--functiongemma-270m-it"
    )
    snapshots_dir = os.path.join(default_cache, "snapshots")
    if os.path.isdir(snapshots_dir):
        snapshots = sorted(
            (os.path.join(snapshots_dir, name) for name in os.listdir(snapshots_dir)),
            key=os.path.getmtime,
        )
        if snapshots:
            return snapshots[-1]
    raise FileNotFoundError(
        "Model path not found. Pass --model-path or set FUNCTIONGEMMA_PATH."
    )


def _program_json_samples() -> list[str]:
    return [
        "[{\"load\":[[\"const\",0,1]]},{\"flow\":[[\"halt\"]]}]",
        "[{\"load\":[[\"const\",0,0]]},{\"flow\":[[\"halt\"]]}]",
        "[{\"alu\":[[\"+\",0,0,0]]},{\"flow\":[[\"halt\"]]}]",
        "[{\"load\":[[\"const\",1,7]]},{\"alu\":[[\"+\",2,1,1]]},{\"flow\":[[\"halt\"]]}]",
    ]


def _variant_names() -> list[str]:
    return [
        "default",
        "kernel_builder_override",
        "cache_top4_d4x15_reset_offload_1013",
        "cache_top4_d4x15_reset_offload_1015_full_window",
        "cache_top4_d4x15_reset_offload_1016",
        "loadbound_preload15_uncached_1316",
    ]


def _proof_names() -> list[str]:
    path = Path(__file__).resolve().parent / "proof_map.json"
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []
    names = [m.get("proof_name") for m in data.get("mappings", [])]
    return [n for n in names if isinstance(n, str) and n]


def _strategy_names() -> list[str]:
    path = Path(__file__).resolve().parent / "proof_strategies.json"
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []
    names = [s.get("name") for s in data.get("strategies", [])]
    return [n for n in names if isinstance(n, str) and n]


def _proof_like_overrides() -> list[dict[str, Any]]:
    return [
        {
            "base_spec": "offload",
            "name_hint": "top4_d4x15_eq_idxshift_off826",
            "overrides": {
                "depth4_rounds": 1,
                "x4": 15,
                "offload_op1": 826,
                "use_bitmask_selection": False,
                "selection_mode": "eq",
                "idx_shifted": True,
                "include_setup": False,
            },
        },
        {
            "base_spec": "offload",
            "name_hint": "top4_d4x15_eq_off911",
            "overrides": {
                "depth4_rounds": 1,
                "x4": 15,
                "offload_op1": 911,
                "use_bitmask_selection": False,
                "selection_mode": "eq",
                "include_setup": False,
            },
        },
        {
            "base_spec": "offload",
            "name_hint": "top3_loadbound_idxshift_ptralu",
            "overrides": {
                "depth4_rounds": 0,
                "x4": 0,
                "cached_nodes": 7,
                "base_cached_rounds": (0, 1, 2, 11, 12, 13),
                "offload_op1": 1510,
                "idx_shifted": True,
                "ptr_setup_engine": "alu",
                "include_setup": False,
                "total_cycles": 1316,
            },
        },
        {
            "base_spec": "offload",
            "name_hint": "mask_idxshift_1012",
            "overrides": {
                "selection_mode": "mask",
                "idx_shifted": True,
                "extra_vecs": 4,
                "vector_block": 4,
                "offload_op1": 1518,
                "total_cycles": 1012,
                "include_setup": False,
            },
        },
        {
            "base_spec": "offload",
            "name_hint": "mask_precompute_idxshift",
            "overrides": {
                "selection_mode": "mask_precompute",
                "idx_shifted": True,
                "extra_vecs": 4,
                "vector_block": 4,
                "include_setup": False,
            },
        },
        {
            "base_spec": "full_isa",
            "name_hint": "parity_off_off448",
            "overrides": {
                "offload_hash_op1": False,
                "offload_parity": True,
                "offload_op1": 448,
            },
        },
        {
            "base_spec": "full_isa",
            "name_hint": "bitmask_idxshift_off1117",
            "overrides": {
                "use_bitmask_selection": True,
                "selection_mode": "bitmask",
                "idx_shifted": True,
                "offload_op1": 1117,
                "depth4_rounds": 0,
                "depth4_cached_rounds": (),
                "x4": 0,
                "total_cycles": 1088,
            },
        },
        {
            "base_spec": "full_isa",
            "name_hint": "bitmask_idxshift_resetflow_off1109",
            "overrides": {
                "use_bitmask_selection": True,
                "selection_mode": "bitmask",
                "idx_shifted": True,
                "reset_on_valu": False,
                "offload_op1": 1109,
                "depth4_rounds": 0,
                "depth4_cached_rounds": (),
                "x4": 0,
                "total_cycles": 1084,
            },
        },
        {
            "base_spec": "full_isa",
            "name_hint": "skip_r3_x4_24_parity_off",
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
                "use_bitmask_selection": False,
            },
        },
    ]


def _random_env_params(rng: random.Random) -> dict[str, Any]:
    heights = [3, 4, 5, 6, 8, 10]
    batches = [8, 16, 32, 64, 128, 256]
    rounds = [1, 2, 4, 8, 16]
    return {
        "forest_height": rng.choice(heights),
        "batch_size": rng.choice(batches),
        "rounds": rng.choice(rounds),
        "seed": rng.randint(0, 100),
    }


def _make_example(user: str, calls: list[dict[str, Any]]) -> dict[str, Any]:
    return {"user": user, "calls": calls}


def build_synthetic_examples(count: int, seed: int) -> list[dict[str, Any]]:
    rng = random.Random(seed)
    variants = _variant_names()
    program_samples = _program_json_samples()

    prompts_get_limits = [
        "Show ISA limits.",
        "What are the slot limits and VLEN?",
        "List the machine caps.",
    ]
    prompts_get_isa_spec = [
        "Show ISA op signatures.",
        "List ISA op arg counts.",
        "Get ISA spec.",
    ]
    prompts_list_op_graph = [
        "List op-graph strategies.",
        "Show op-graph templates.",
        "What op-graph strategies are available?",
    ]
    prompts_list_variants = [
        "List kernel variants.",
        "What kernel builder variants are available?",
        "Show available kernel variants.",
    ]
    prompts_sweep = [
        "Sweep caps for T={T} with depth4_rounds={d4} and X={x}.",
        "Find feasible cap configs for T={T} with setup_valu={sv}.",
        "Sweep caps with flow setup {flow} and shifts on {shift} for T={T}.",
    ]
    prompts_run_variant = [
        "Run variant {v} on the frozen test case.",
        "Run kernel variant {v} with height 10, rounds 16, batch 256.",
        "Execute variant {v} with seed {seed}.",
        "Run proof variant {v} on the frozen test case.",
    ]
    prompts_compare = [
        "Compare all variants on the frozen test case.",
        "Compare kernel variants and return the best cycle count.",
        "Compare variants {v1} and {v2} on height 10, rounds 16, batch 256.",
    ]
    prompts_create_variant = [
        "Create variant {name} based on {base}.",
        "Write a new variant {name} using base spec {base}.",
        "Create a kernel variant {name} with overrides.",
        "Create variant {name} from base spec {base} with overrides.",
        "Scaffold variant {name} on {base} and register it.",
    ]
    proof_names = _proof_names()
    schedule_specs = proof_names or [
        "cache_top4_d4x15_reset_offload_1013",
        "cache_top4_d4x15_reset_offload_1015_full_window",
        "cache_top4_d4x15_reset_offload_1016",
        "loadbound_preload15_uncached_1316",
    ]
    schedule_specs = sorted(set(schedule_specs + ["base", "offload", "full_isa"]))
    strategy_names = _strategy_names() or schedule_specs
    proof_overrides = _proof_like_overrides()
    prompts_schedule_summary = [
        "Summarize schedule stats for spec {spec}.",
        "Show schedule utilization for {spec}.",
        "Get schedule summary for spec {spec}.",
        "Report bottlenecks for {spec} and note the tightest engine.",
    ]
    prompts_find_mismatch = [
        "Find the first schedule mismatch for spec {spec}.",
        "Check schedule dependencies for spec {spec}.",
        "Locate the first dependency mismatch in spec {spec}.",
    ]
    prompts_sweep_proof = [
        "Sweep proof strategies from the default config.",
        "Run proof strategy sweep for {strategy}.",
        "Sweep proof strategies with T={T}.",
        "Run proof strategy sweep for {strategy} with T={T}.",
        "Find the lowest feasible T for proof strategy {strategy}.",
        "Check proof strategy {strategy} for low-cycle feasibility.",
    ]
    prompts_make_env = [
        "Create env height {h}, batch {b}, rounds {r}, seed {s}.",
        "Make env with height {h}, batch {b}, rounds {r}.",
        "Create a frozen env height {h} batch {b} rounds {r} seed {s}.",
    ]
    prompts_reset_env = [
        "Reset env {eid}.",
        "Reset environment {eid} to initial state.",
        "Reinitialize env {eid}.",
    ]
    prompts_run = [
        "Run env {eid}.",
        "Run env {eid} for at most {mc} cycles.",
        "Run env {eid} for {mi} instructions.",
    ]
    prompts_step = [
        "Step env {eid} by {n} instructions.",
        "Advance env {eid} by {n} steps.",
    ]
    prompts_read_mem = [
        "Read memory {start}..{end} from env {eid}.",
        "Read mem start {start} length {length} from env {eid}.",
    ]
    prompts_read_scratch = [
        "Read scratch {addrs} from env {eid}.",
        "Read scratch addresses {addrs} on env {eid}.",
    ]
    prompts_validate = [
        "Validate this program json.",
        "Check if this program json is valid.",
    ]
    prompts_set_program = [
        "Set env {eid} program to this json.",
        "Update env {eid} with the program json.",
    ]
    prompts_create_variant_opt = [
        "Create a proof-aligned variant {name} from {base}.",
        "Create a low-cycle variant {name} using {base} with optimized overrides.",
        "Scaffold a proof-inspired variant {name} on base {base}.",
    ]
    prompts_create_op_graph = [
        "Create op-graph variant {name} using strategy {strategy}.",
        "Scaffold op-graph variant {name} with {strategy}.",
        "Make op-graph variant {name} from template {strategy}.",
    ]
    prompts_assemble_instruction = [
        "Assemble an instruction bundle with a const load and halt.",
        "Create a single instruction with an add and a load.",
        "Build an instruction bundle with a vload.",
    ]
    prompts_assemble_program = [
        "Assemble a program with a const then halt.",
        "Create a program list with two instructions.",
        "Build a short program with a load and halt.",
    ]
    prompts_validate_ops = [
        "Validate this program json with op checks.",
        "Check op signatures for this program json.",
        "Validate program ops for this json.",
    ]
    prompts_run_program = [
        "Run this program json as a smoke test.",
        "Execute this program json for a few steps.",
        "Run this program json for at most 4 instructions.",
    ]

    examples: list[dict[str, Any]] = []

    tool_weights = [
        ("get_limits", 4),
        ("get_isa_spec", 4),
        ("list_variants", 4),
        ("list_op_graph_strategies", 4),
        ("sweep_caps", 8),
        ("run_variant", 8),
        ("compare_variants", 8),
        ("create_variant", 8),
        ("create_op_graph_variant", 6),
        ("schedule_summary", 8),
        ("find_schedule_mismatch", 6),
        ("sweep_proof_strategies", 8),
        ("make_env", 6),
        ("reset_env", 4),
        ("run", 6),
        ("step", 4),
        ("read_mem", 3),
        ("read_scratch", 3),
        ("validate_program", 2),
        ("set_program", 2),
        ("assemble_instruction", 2),
        ("assemble_program", 2),
        ("validate_program_ops", 2),
        ("run_program", 2),
        ("multi", 6),
    ]
    tool_choices = [t for t, w in tool_weights for _ in range(w)]

    for _ in range(count):
        choice = rng.choice(tool_choices)
        if choice == "get_limits":
            examples.append(
                _make_example(
                    rng.choice(prompts_get_limits),
                    [{"name": "get_limits", "arguments": {}}],
                )
            )
        elif choice == "get_isa_spec":
            examples.append(
                _make_example(
                    rng.choice(prompts_get_isa_spec),
                    [{"name": "get_isa_spec", "arguments": {"use_frozen": True}}],
                )
            )
        elif choice == "list_op_graph_strategies":
            examples.append(
                _make_example(
                    rng.choice(prompts_list_op_graph),
                    [{"name": "list_op_graph_strategies", "arguments": {}}],
                )
            )
        elif choice == "list_variants":
            examples.append(
                _make_example(
                    rng.choice(prompts_list_variants),
                    [{"name": "list_variants", "arguments": {}}],
                )
            )
        elif choice == "sweep_caps":
            T = rng.choice([1012, 1013, 1016, 1084, 1088, 1174, 1227, 1312, 1316, 1456, 1577, 1615, 1647, 1726])
            d4 = rng.choice([0, 1, 2])
            x = rng.choice([0, 8, 15, 24, 32])
            setup = rng.choice([0, 16, 32, 45, 48])
            flow = rng.choice([0, 64])
            shift = rng.choice([True, False])
            user = rng.choice(prompts_sweep).format(
                T=T, d4=d4, x=x, sv=setup, flow=flow, shift=("alu" if shift else "valu")
            )
            args = {
                "T_values": [T],
                "depth4_rounds": [d4],
                "setup_valu": [setup],
                "x_values": [x],
                "flow_setup_ops": [flow],
                "shift_on_alu": [shift],
                "reset_on_flow": [rng.choice([True, False])],
                "max_results_per_config": 10,
            }
            examples.append(_make_example(user, [{"name": "sweep_caps", "arguments": args}]))
        elif choice == "run_variant":
            v = rng.choice(variants)
            seed_val = rng.randint(0, 100)
            user = rng.choice(prompts_run_variant).format(v=v, seed=seed_val)
            args = {
                "variant": v,
                "forest_height": 10,
                "rounds": 16,
                "batch_size": 256,
                "seed": seed_val,
                "use_frozen": True,
                "check_correctness": True,
            }
            examples.append(_make_example(user, [{"name": "run_variant", "arguments": args}]))
        elif choice == "compare_variants":
            v1, v2 = rng.sample(variants, 2)
            user = rng.choice(prompts_compare).format(v1=v1, v2=v2)
            args = {
                "variants": None if rng.random() < 0.5 else [v1, v2],
                "forest_height": 10,
                "rounds": 16,
                "batch_size": 256,
                "seed": rng.randint(0, 100),
                "use_frozen": True,
                "check_correctness": True,
            }
            examples.append(_make_example(user, [{"name": "compare_variants", "arguments": args}]))
        elif choice == "create_variant":
            use_proof = rng.random() < 0.65 and proof_overrides
            if use_proof:
                tmpl = rng.choice(proof_overrides)
                base = tmpl["base_spec"]
                name = f"autogen_{tmpl['name_hint']}_{rng.randint(0, 9999)}"
                overrides = dict(tmpl["overrides"])
                user = rng.choice(prompts_create_variant_opt).format(name=name, base=base)
            else:
                base = rng.choice(["offload", "full_isa"])
                name = f"autogen_{base}_{rng.randint(0, 9999)}"
                if base == "offload":
                    overrides = {
                        "depth4_rounds": rng.choice([0, 1, 2]),
                        "x4": rng.choice([0, 8, 15, 24, 32]),
                        "offload_op1": rng.choice([0, 400, 826, 1200, 1518]),
                        "use_bitmask_selection": rng.choice([True, False]),
                        "selection_mode": rng.choice(["eq", "bitmask", "mask", "mask_precompute"]),
                        "idx_shifted": rng.choice([True, False]),
                        "ptr_setup_engine": rng.choice(["flow", "alu"]),
                        "reset_on_valu": rng.choice([True, False]),
                        "shifts_on_valu": rng.choice([True, False]),
                    }
                else:
                    overrides = {
                        "depth4_rounds": rng.choice([0, 1, 2]),
                        "x4": rng.choice([0, 8, 15, 24, 32]),
                        "offload_op1": rng.choice([0, 400, 800, 1024, 1117]),
                        "use_bitmask_selection": rng.choice([True, False]),
                        "selection_mode": rng.choice(["eq", "bitmask", "mask", "mask_precompute"]),
                        "idx_shifted": rng.choice([True, False]),
                        "ptr_setup_engine": rng.choice(["flow", "alu"]),
                        "reset_on_valu": rng.choice([True, False]),
                        "shifts_on_valu": rng.choice([True, False]),
                        "offload_hash_op1": rng.choice([True, False]),
                        "offload_parity": rng.choice([True, False]),
                    }
                user = rng.choice(prompts_create_variant).format(name=name, base=base)
                if rng.random() < 0.2:
                    overrides = {}
            register = rng.random() < 0.85
            overwrite = rng.random() < 0.1
            examples.append(
                _make_example(
                    user,
                    [
                        {
                            "name": "create_variant",
                            "arguments": {
                                "name": name,
                                "base_spec": base,
                                "overrides": overrides,
                                "register": register,
                                "overwrite": overwrite,
                            },
                        }
                    ],
                )
            )
        elif choice == "create_op_graph_variant":
            strategies = [
                "mask_precompute_idxshift",
                "mask_idxshift",
                "bitmask_idxshift",
                "bitmask_idxshift_resetflow",
                "top3_loadbound_ptralu",
                "skip_r3_x4_24_parity_off",
            ]
            strategy = rng.choice(strategies)
            name = f"autograph_{strategy}_{rng.randint(0, 9999)}"
            user = rng.choice(prompts_create_op_graph).format(name=name, strategy=strategy)
            examples.append(
                _make_example(
                    user,
                    [
                        {
                            "name": "create_op_graph_variant",
                            "arguments": {
                                "name": name,
                                "strategy": strategy,
                                "register": True,
                            },
                        }
                    ],
                )
            )
        elif choice == "schedule_summary":
            spec = rng.choice(schedule_specs)
            user = rng.choice(prompts_schedule_summary).format(spec=spec)
            examples.append(_make_example(user, [{"name": "schedule_summary", "arguments": {"spec": spec}}]))
        elif choice == "find_schedule_mismatch":
            spec = rng.choice(schedule_specs)
            user = rng.choice(prompts_find_mismatch).format(spec=spec)
            args = {
                "spec": spec,
                "forest_height": 10,
                "rounds": 16,
                "batch_size": 256,
                "seed": rng.randint(0, 100),
                "use_frozen": True,
                "max_ops": None,
            }
            examples.append(_make_example(user, [{"name": "find_schedule_mismatch", "arguments": args}]))
        elif choice == "sweep_proof_strategies":
            strategy = rng.choice(strategy_names)
            T = rng.choice([1012, 1013, 1016, 1084, 1088, 1174, 1227, 1312, 1316, 1456, 1577, 1615])
            user = rng.choice(prompts_sweep_proof).format(strategy=strategy, T=T)
            args: dict[str, Any] = {}
            if "strategy" in user:
                args["strategy"] = strategy
            if "T=" in user:
                args["T_values"] = [T]
            examples.append(
                _make_example(
                    user,
                    [
                        {
                            "name": "sweep_proof_strategies",
                            "arguments": args,
                        }
                    ],
                )
            )
        elif choice == "make_env":
            params = _random_env_params(rng)
            use_frozen = rng.random() < 0.4
            enable_debug = rng.random() < 0.2
            user = rng.choice(prompts_make_env).format(
                h=params["forest_height"],
                b=params["batch_size"],
                r=params["rounds"],
                s=params["seed"],
            )
            args = dict(params)
            if "frozen env" in user:
                args["use_frozen"] = True
            else:
                args["use_frozen"] = use_frozen
            if enable_debug:
                args["enable_debug"] = True
            examples.append(_make_example(user, [{"name": "make_env", "arguments": args}]))
        elif choice == "reset_env":
            env_id = rng.randint(0, 3)
            user = rng.choice(prompts_reset_env).format(eid=env_id)
            examples.append(_make_example(user, [{"name": "reset_env", "arguments": {"env_id": env_id}}]))
        elif choice == "run":
            env_id = rng.randint(0, 3)
            if rng.random() < 0.5:
                max_cycles = rng.choice([50, 100, 200])
                user = rng.choice(prompts_run).format(eid=env_id, mc=max_cycles, mi=0)
                args = {"env_id": env_id, "max_cycles": max_cycles}
            else:
                max_instr = rng.choice([5, 10, 25])
                user = rng.choice(prompts_run).format(eid=env_id, mc=0, mi=max_instr)
                args = {"env_id": env_id, "max_instructions": max_instr}
            examples.append(_make_example(user, [{"name": "run", "arguments": args}]))
        elif choice == "step":
            env_id = rng.randint(0, 3)
            n = rng.randint(1, 5)
            user = rng.choice(prompts_step).format(eid=env_id, n=n)
            examples.append(_make_example(user, [{"name": "step", "arguments": {"env_id": env_id, "n": n}}]))
        elif choice == "read_mem":
            env_id = rng.randint(0, 3)
            start = rng.choice([0, 4, 8, 16, 32])
            length = rng.choice([4, 8, 16])
            user = rng.choice(prompts_read_mem).format(eid=env_id, start=start, end=start + length, length=length)
            examples.append(
                _make_example(
                    user,
                    [{"name": "read_mem", "arguments": {"env_id": env_id, "start": start, "length": length}}],
                )
            )
        elif choice == "read_scratch":
            env_id = rng.randint(0, 3)
            addrs = rng.sample(range(0, 16), rng.randint(1, 4))
            addrs_str = ",".join(str(a) for a in addrs)
            user = rng.choice(prompts_read_scratch).format(eid=env_id, addrs=addrs_str)
            examples.append(
                _make_example(
                    user,
                    [{"name": "read_scratch", "arguments": {"env_id": env_id, "addrs": addrs}}],
                )
            )
        elif choice == "validate_program":
            program_json = rng.choice(program_samples)
            user = rng.choice(prompts_validate)
            examples.append(
                _make_example(
                    user,
                    [{"name": "validate_program", "arguments": {"program_json": program_json}}],
                )
            )
        elif choice == "set_program":
            env_id = rng.randint(0, 3)
            program_json = rng.choice(program_samples)
            user = rng.choice(prompts_set_program).format(eid=env_id)
            examples.append(
                _make_example(
                    user,
                    [{"name": "set_program", "arguments": {"env_id": env_id, "program_json": program_json}}],
                )
            )
        elif choice == "assemble_instruction":
            instr = {"load": [["const", 0, 1]], "flow": [["halt"]]}
            examples.append(
                _make_example(
                    rng.choice(prompts_assemble_instruction),
                    [
                        {
                            "name": "assemble_instruction",
                            "arguments": {"slots": instr, "validate": True, "use_frozen": True},
                        }
                    ],
                )
            )
        elif choice == "assemble_program":
            program = [
                {"load": [["const", 0, 1]]},
                {"flow": [["halt"]]},
            ]
            examples.append(
                _make_example(
                    rng.choice(prompts_assemble_program),
                    [
                        {
                            "name": "assemble_program",
                            "arguments": {"instructions": program, "validate": True, "use_frozen": True},
                        }
                    ],
                )
            )
        elif choice == "validate_program_ops":
            program_json = rng.choice(program_samples)
            examples.append(
                _make_example(
                    rng.choice(prompts_validate_ops),
                    [
                        {
                            "name": "validate_program_ops",
                            "arguments": {"program_json": program_json, "use_frozen": True},
                        }
                    ],
                )
            )
        elif choice == "run_program":
            program_json = rng.choice(program_samples)
            examples.append(
                _make_example(
                    rng.choice(prompts_run_program),
                    [
                        {
                            "name": "run_program",
                            "arguments": {
                                "program_json": program_json,
                                "max_instructions": 4,
                                "use_frozen": True,
                            },
                        }
                    ],
                )
            )
        else:
            if rng.random() < 0.5:
                spec = rng.choice(schedule_specs)
                user = f"Sweep proof strategies and summarize schedule for {spec}."
                examples.append(
                    _make_example(
                        user,
                        [
                            {"name": "sweep_proof_strategies", "arguments": {"max_results_per_strategy": 5}},
                            {"name": "schedule_summary", "arguments": {"spec": spec}},
                        ],
                    )
                )
            else:
                tmpl = rng.choice(proof_overrides) if proof_overrides else None
                if tmpl:
                    base = tmpl["base_spec"]
                    name = f"autogen_{tmpl['name_hint']}_{rng.randint(0, 9999)}"
                    overrides = dict(tmpl["overrides"])
                else:
                    base = rng.choice(["offload", "full_isa"])
                    name = f"autogen_{base}_{rng.randint(0, 9999)}"
                    overrides = {}
                if rng.random() < 0.5:
                    strategy = rng.choice(
                        [
                            "mask_precompute_idxshift",
                            "mask_idxshift",
                            "bitmask_idxshift",
                            "bitmask_idxshift_resetflow",
                            "top3_loadbound_ptralu",
                            "skip_r3_x4_24_parity_off",
                        ]
                    )
                    name = f"autograph_{strategy}_{rng.randint(0, 9999)}"
                    user = f"Create op-graph variant {name} and run it on the frozen test case."
                    calls = [
                        {"name": "list_op_graph_strategies", "arguments": {}},
                        {
                            "name": "create_op_graph_variant",
                            "arguments": {"name": name, "strategy": strategy, "register": True},
                        },
                        {
                            "name": "run_variant",
                            "arguments": {
                                "variant": name,
                                "forest_height": 10,
                                "rounds": 16,
                                "batch_size": 256,
                                "seed": 0,
                                "use_frozen": True,
                                "check_correctness": True,
                            },
                        },
                    ]
                else:
                    user = f"Create variant {name} and run it on the frozen test case."
                    calls = [
                        {
                            "name": "create_variant",
                            "arguments": {
                                "name": name,
                                "base_spec": base,
                                "overrides": overrides,
                                "register": True,
                            },
                        },
                        {
                            "name": "run_variant",
                            "arguments": {
                                "variant": name,
                                "forest_height": 10,
                                "rounds": 16,
                                "batch_size": 256,
                                "seed": 0,
                                "use_frozen": True,
                                "check_correctness": True,
                            },
                        },
                    ]
                examples.append(_make_example(user, calls))

    return examples


def create_conversation(sample: dict[str, Any], tools: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "messages": [
            {"role": "developer", "content": DEFAULT_SYSTEM_MSG},
            {"role": "user", "content": sample["user"]},
            {
                "role": "assistant",
                "tool_calls": [
                    {"type": "function", "function": call} for call in sample["calls"]
                ],
            },
        ],
        "tools": tools,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-path")
    parser.add_argument("--dataset-in", help="Optional JSONL dataset to use instead of synthetic examples.")
    parser.add_argument("--output-dir", default="functiongemma-tools-ft")
    parser.add_argument("--epochs", type=int, default=3)
    parser.add_argument("--batch-size", type=int, default=1)
    parser.add_argument("--grad-accum", type=int, default=4)
    parser.add_argument("--max-length", type=int, default=512)
    parser.add_argument("--learning-rate", type=float, default=5e-5)
    parser.add_argument("--max-steps", type=int)
    parser.add_argument("--device")
    parser.add_argument("--synthetic-size", type=int, default=2000)
    parser.add_argument("--synthetic-seed", type=int, default=42)
    parser.add_argument("--dataset-out", help="Optional path to write JSONL dataset.")
    args = parser.parse_args()

    model_path = resolve_model_path(args.model_path)

    device = args.device
    if device is None:
        device = "mps" if torch.backends.mps.is_available() else "cpu"

    processor = AutoProcessor.from_pretrained(model_path, local_files_only=True)
    tokenizer = getattr(processor, "tokenizer", None)
    if tokenizer is None:
        tokenizer = AutoTokenizer.from_pretrained(model_path, local_files_only=True)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    chat_template = getattr(tokenizer, "chat_template", None)
    if not chat_template:
        template_path = Path(model_path) / "chat_template.jinja"
        if template_path.exists():
            chat_template = template_path.read_text(encoding="utf-8")
    tools = [get_json_schema(fn) for fn in TOOL_FUNCS]

    if args.dataset_in:
        samples: list[dict[str, Any]] = []
        with open(args.dataset_in, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                samples.append(json.loads(line))
    else:
        samples = build_synthetic_examples(args.synthetic_size, args.synthetic_seed)

    def _sample_to_text(sample: dict[str, Any]) -> dict[str, Any]:
        if "messages" in sample:
            messages = sample["messages"]
            tool_spec = sample.get("tools", tools)
        else:
            conv = create_conversation(sample, tools)
            messages = conv["messages"]
            tool_spec = conv["tools"]
        text = processor.apply_chat_template(
            messages,
            tools=tool_spec,
            add_generation_prompt=False,
            tokenize=False,
            chat_template=chat_template,
        )
        return {"text": text}

    text_rows = [_sample_to_text(sample) for sample in samples]
    dataset = Dataset.from_list(text_rows)
    dataset = dataset.train_test_split(test_size=0.2, shuffle=True, seed=42)

    if args.dataset_out:
        out_path = Path(args.dataset_out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with out_path.open("w", encoding="utf-8") as f:
            for row in dataset["train"]:
                f.write(json.dumps(row) + "\n")
            for row in dataset["test"]:
                f.write(json.dumps(row) + "\n")

    # MPS + fp16 tends to produce NaNs; keep fp32 on MPS.
    use_fp16 = device == "cuda"
    torch_dtype = torch.float16 if use_fp16 else torch.float32
    model = AutoModelForCausalLM.from_pretrained(
        model_path,
        torch_dtype=torch_dtype,
        local_files_only=True,
    )

    target_modules = []
    for name, module in model.named_modules():
        if name.endswith(("q_proj", "k_proj", "v_proj", "o_proj")):
            target_modules.append(name.split(".")[-1])
    if not target_modules:
        target_modules = ["q_proj", "v_proj"]

    lora_config = LoraConfig(
        r=8,
        lora_alpha=16,
        lora_dropout=0.05,
        target_modules=sorted(set(target_modules)),
    )
    model = get_peft_model(model, lora_config)
    model.to(device)

    max_steps = args.max_steps if args.max_steps is not None else -1
    sft_args = SFTConfig(
        output_dir=args.output_dir,
        max_length=args.max_length,
        packing=False,
        num_train_epochs=args.epochs,
        per_device_train_batch_size=args.batch_size,
        gradient_accumulation_steps=args.grad_accum,
        learning_rate=args.learning_rate,
        logging_steps=1,
        eval_strategy="epoch",
        save_strategy="epoch",
        report_to="none",
        optim="adamw_torch",
        gradient_checkpointing=False,
        fp16=use_fp16,
        bf16=False,
        max_steps=max_steps,
        dataset_text_field="text",
    )

    trainer = SFTTrainer(
        model=model,
        args=sft_args,
        train_dataset=dataset["train"],
        eval_dataset=dataset["test"],
        processing_class=tokenizer,
    )

    trainer.train()
    trainer.save_model()


if __name__ == "__main__":
    main()
