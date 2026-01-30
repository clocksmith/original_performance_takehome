from __future__ import annotations

import argparse
import os
import re
from pathlib import Path
from typing import Any

import torch
from transformers import AutoModelForCausalLM, AutoProcessor
from transformers.utils import get_json_schema

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
    env_path = Path("~/.cache/huggingface/hub/models--google--functiongemma-270m-it").expanduser()
    if env_path.exists():
        snapshots = sorted((env_path / "snapshots").glob("*"), key=lambda p: p.stat().st_mtime)
        if snapshots:
            return str(snapshots[-1])
    raise FileNotFoundError(
        "Model path not found. Pass --model-path or set FUNCTIONGEMMA_PATH."
    )


def extract_tool_calls(text: str) -> list[dict[str, Any]]:
    def cast(v: str) -> Any:
        v = v.strip()
        if v.lower() in {"true", "false"}:
            return v.lower() == "true"
        try:
            return int(v)
        except ValueError:
            try:
                return float(v)
            except ValueError:
                return v.strip("\"'")

    calls = []
    for name, args in re.findall(
        r"<start_function_call>call:(\w+)\{(.*?)\}<end_function_call>",
        text,
        re.DOTALL,
    ):
        arg_pairs = re.findall(
            r"(\w+):(?:<escape>(.*?)<escape>|([^,}]*))", args
        )
        parsed_args = {
            k: cast((v1 or v2).strip()) for k, v1, v2 in arg_pairs if k
        }
        calls.append({"name": name, "arguments": parsed_args})
    return calls


def build_tools() -> list[dict[str, Any]]:
    return [get_json_schema(fn) for fn in TOOL_FUNCS]


def get_device(device_arg: str | None) -> str:
    if device_arg:
        return device_arg
    if torch.backends.mps.is_available():
        return "mps"
    return "cpu"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prompt", required=True)
    parser.add_argument("--model-path")
    parser.add_argument("--max-new-tokens", type=int, default=128)
    parser.add_argument("--max-turns", type=int, default=4)
    parser.add_argument("--device")
    parser.add_argument("--show-raw", action="store_true")
    args = parser.parse_args()

    model_path = resolve_model_path(args.model_path)
    device = get_device(args.device)

    processor = AutoProcessor.from_pretrained(model_path, local_files_only=True)
    tokenizer = getattr(processor, "tokenizer", None)
    chat_template = getattr(tokenizer, "chat_template", None) if tokenizer else None
    if not chat_template:
        template_path = Path(model_path) / "chat_template.jinja"
        if template_path.exists():
            chat_template = template_path.read_text(encoding="utf-8")

    model = AutoModelForCausalLM.from_pretrained(
        model_path, torch_dtype="auto", local_files_only=True
    )
    model.to(device)

    tools = build_tools()

    messages: list[dict[str, Any]] = [
        {"role": "developer", "content": DEFAULT_SYSTEM_MSG},
        {"role": "user", "content": args.prompt},
    ]

    for _ in range(args.max_turns):
        inputs = processor.apply_chat_template(
            messages,
            tools=tools,
            add_generation_prompt=True,
            return_tensors="pt",
            return_dict=True,
            chat_template=chat_template,
        )
        inputs = {k: v.to(device) for k, v in inputs.items()}

        out = model.generate(
            **inputs,
            pad_token_id=processor.eos_token_id,
            max_new_tokens=args.max_new_tokens,
        )
        gen_tokens = out[0][len(inputs["input_ids"][0]) :]
        output = processor.decode(gen_tokens, skip_special_tokens=True)

        if args.show_raw:
            print("RAW:", output)

        calls = extract_tool_calls(output)
        if not calls:
            print(output)
            return

        tool_map = {fn.__name__: fn for fn in TOOL_FUNCS}
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
                results.append(
                    {"name": call["name"], "response": {"error": "unknown tool"}}
                )
                continue
            try:
                response = fn(**call["arguments"])
            except Exception as exc:  # pragma: no cover - debug aid
                response = {"error": f"{type(exc).__name__}: {exc}"}
            results.append({"name": call["name"], "response": response})

        messages.append({"role": "tool", "content": results})

    print("Reached max turns without final response.")


if __name__ == "__main__":
    main()
