from __future__ import annotations

import argparse
import json
import random
from pathlib import Path
from typing import Any

import torch
from transformers import AutoModelForCausalLM, AutoProcessor

from functiongemma_infer import (
    DEFAULT_SYSTEM_MSG,
    build_tools,
    extract_tool_calls,
    get_device,
    resolve_model_path,
)
from functiongemma_tools import TOOL_FUNCS


def _default_prompts() -> list[str]:
    return [
        "Find the lowest cycle count for the frozen test case. Use tools.",
        "Compare kernel variants on the frozen test case and return the best.",
        "Create a new kernel variant and run it on the frozen test case.",
        "Search for a faster variant and validate correctness.",
    ]


def _load_prompts(prompt: str | None, prompt_file: str | None) -> list[str]:
    if prompt:
        return [prompt]
    if prompt_file:
        path = Path(prompt_file)
        if not path.exists():
            raise FileNotFoundError(f"Prompt file not found: {path}")
        lines = [line.strip() for line in path.read_text(encoding="utf-8").splitlines()]
        return [line for line in lines if line]
    return _default_prompts()


def _collect_cycles(resp: Any, cycles: list[int]) -> None:
    if isinstance(resp, dict):
        if resp.get("ok") is False:
            return
        if isinstance(resp.get("cycle"), int):
            cycles.append(resp["cycle"])
        best = resp.get("best")
        if isinstance(best, dict) and best.get("ok") and isinstance(best.get("cycle"), int):
            cycles.append(best["cycle"])
        results = resp.get("results")
        if isinstance(results, list):
            for item in results:
                _collect_cycles(item, cycles)
        return
    if isinstance(resp, list):
        for item in resp:
            _collect_cycles(item, cycles)


def _run_trajectory(
    model: Any,
    processor: Any,
    tools: list[dict[str, Any]],
    tool_map: dict[str, Any],
    prompt: str,
    device: str,
    max_new_tokens: int,
    max_turns: int,
    temperature: float,
    top_p: float,
    seed: int | None,
) -> dict[str, Any]:
    if seed is not None:
        random.seed(seed)
        torch.manual_seed(seed)

    messages: list[dict[str, Any]] = [
        {"role": "developer", "content": DEFAULT_SYSTEM_MSG},
        {"role": "user", "content": prompt},
    ]
    all_tool_calls: list[dict[str, Any]] = []

    for _ in range(max_turns):
        inputs = processor.apply_chat_template(
            messages,
            tools=tools,
            add_generation_prompt=True,
            return_tensors="pt",
            return_dict=True,
        )
        inputs = {k: v.to(device) for k, v in inputs.items()}

        out = model.generate(
            **inputs,
            pad_token_id=processor.eos_token_id,
            max_new_tokens=max_new_tokens,
            do_sample=temperature > 0,
            temperature=temperature,
            top_p=top_p,
        )
        gen_tokens = out[0][len(inputs["input_ids"][0]) :]
        output = processor.decode(gen_tokens, skip_special_tokens=True)

        calls = extract_tool_calls(output)
        if not calls:
            break

        all_tool_calls.extend(calls)
        messages.append(
            {
                "role": "assistant",
                "tool_calls": [
                    {"type": "function", "function": call} for call in calls
                ],
            }
        )

        results = []
        for call in calls:
            fn = tool_map.get(call["name"])
            if fn is None:
                results.append({"name": call["name"], "response": {"error": "unknown tool"}})
                continue
            try:
                response = fn(**call["arguments"])
            except Exception as exc:  # pragma: no cover - debug aid
                response = {"error": f"{type(exc).__name__}: {exc}"}
            results.append({"name": call["name"], "response": response})

        messages.append({"role": "tool", "content": results})

    cycles: list[int] = []
    for item in messages:
        if item.get("role") != "tool":
            continue
        content = item.get("content")
        if not isinstance(content, list):
            continue
        for entry in content:
            _collect_cycles(entry.get("response"), cycles)

    best_cycle = min(cycles) if cycles else None
    reward = -best_cycle if best_cycle is not None else None

    return {
        "prompt": prompt,
        "messages": messages,
        "tools": tools,
        "calls": all_tool_calls,
        "best_cycle": best_cycle,
        "reward": reward,
    }


def _load_model(model_path: str, device: str, lora_path: str | None, merge_lora: bool) -> Any:
    model = AutoModelForCausalLM.from_pretrained(
        model_path, torch_dtype="auto", local_files_only=True
    )
    if lora_path:
        try:
            from peft import PeftModel
        except ImportError as exc:  # pragma: no cover - optional dependency
            raise ImportError("peft is required for --lora-path") from exc
        model = PeftModel.from_pretrained(model, lora_path, is_trainable=False)
        if merge_lora:
            model = model.merge_and_unload()
    model.to(device)
    return model


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prompt")
    parser.add_argument("--prompt-file")
    parser.add_argument("--model-path")
    parser.add_argument("--device")
    parser.add_argument("--max-new-tokens", type=int, default=160)
    parser.add_argument("--max-turns", type=int, default=4)
    parser.add_argument("--temperature", type=float, default=0.7)
    parser.add_argument("--top-p", type=float, default=0.95)
    parser.add_argument("--samples-per-prompt", type=int, default=6)
    parser.add_argument("--keep-top-k", type=int, default=1)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--out", default="selfplay.jsonl")
    parser.add_argument("--lora-path", help="Optional LoRA adapter directory")
    parser.add_argument("--merge-lora", action="store_true", help="Merge LoRA weights into base model")
    args = parser.parse_args()

    prompts = _load_prompts(args.prompt, args.prompt_file)

    model_path = resolve_model_path(args.model_path)
    device = get_device(args.device)
    processor = AutoProcessor.from_pretrained(model_path, local_files_only=True)
    model = _load_model(model_path, device, args.lora_path, args.merge_lora)

    tools = build_tools()
    tool_map = {fn.__name__: fn for fn in TOOL_FUNCS}

    records: list[dict[str, Any]] = []
    rng = random.Random(args.seed)
    for prompt in prompts:
        prompt_records: list[dict[str, Any]] = []
        for i in range(args.samples_per_prompt):
            sample_seed = rng.randint(0, 1_000_000)
            record = _run_trajectory(
                model=model,
                processor=processor,
                tools=tools,
                tool_map=tool_map,
                prompt=prompt,
                device=device,
                max_new_tokens=args.max_new_tokens,
                max_turns=args.max_turns,
                temperature=args.temperature,
                top_p=args.top_p,
                seed=sample_seed,
            )
            prompt_records.append(record)

        valid = [r for r in prompt_records if r["best_cycle"] is not None]
        valid.sort(key=lambda r: r["best_cycle"])
        keep = valid[: max(1, args.keep_top_k)] if valid else []
        records.extend(keep)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        for row in records:
            f.write(json.dumps(row) + "\n")

    print(f"Wrote {len(records)} records to {out_path}")


if __name__ == "__main__":
    main()
