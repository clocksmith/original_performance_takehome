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
    ]
    prompts_compare = [
        "Compare all variants on the frozen test case.",
        "Compare kernel variants and return the best cycle count.",
        "Compare variants {v1} and {v2} on height 10, rounds 16, batch 256.",
    ]
    prompts_make_env = [
        "Create env height {h}, batch {b}, rounds {r}, seed {s}.",
        "Make env with height {h}, batch {b}, rounds {r}.",
        "Create a frozen env height {h} batch {b} rounds {r} seed {s}.",
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

    examples: list[dict[str, Any]] = []

    tool_weights = [
        ("get_limits", 4),
        ("list_variants", 4),
        ("sweep_caps", 6),
        ("run_variant", 6),
        ("compare_variants", 6),
        ("make_env", 8),
        ("run", 8),
        ("step", 6),
        ("read_mem", 6),
        ("read_scratch", 6),
        ("validate_program", 4),
        ("set_program", 4),
        ("multi", 4),
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
        elif choice == "list_variants":
            examples.append(
                _make_example(
                    rng.choice(prompts_list_variants),
                    [{"name": "list_variants", "arguments": {}}],
                )
            )
        elif choice == "sweep_caps":
            T = rng.choice([1013, 1016])
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
        else:
            user = "Show ISA limits and list kernel variants."
            examples.append(
                _make_example(
                    user,
                    [
                        {"name": "get_limits", "arguments": {}},
                        {"name": "list_variants", "arguments": {}},
                    ],
                )
            )

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

    examples = build_synthetic_examples(args.synthetic_size, args.synthetic_seed)
    dataset = Dataset.from_list(examples)
    dataset = dataset.map(lambda s: create_conversation(s, tools), remove_columns=dataset.column_names)

    def _to_text(sample: dict[str, Any]) -> dict[str, Any]:
        text = processor.apply_chat_template(
            sample["messages"],
            tools=sample["tools"],
            add_generation_prompt=False,
            tokenize=False,
            chat_template=chat_template,
        )
        return {"text": text}

    dataset = dataset.map(_to_text, remove_columns=dataset.column_names)
    dataset = dataset.train_test_split(test_size=0.2, shuffle=True, seed=42)

    if args.dataset_out:
        out_path = Path(args.dataset_out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with out_path.open("w", encoding="utf-8") as f:
            for row in dataset["train"]:
                f.write(json.dumps(row) + "\n")
            for row in dataset["test"]:
                f.write(json.dumps(row) + "\n")

    torch_dtype = torch.float16 if device == "mps" else torch.float32
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
        fp16=True if device == "mps" else False,
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
