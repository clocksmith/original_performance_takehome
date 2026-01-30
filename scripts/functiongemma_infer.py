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
    escape_token = "<escape>"

    def split_top_level(value: str) -> list[str]:
        parts: list[str] = []
        buf: list[str] = []
        depth = 0
        in_escape = False
        i = 0
        while i < len(value):
            if value.startswith(escape_token, i):
                in_escape = not in_escape
                i += len(escape_token)
                continue
            ch = value[i]
            if not in_escape:
                if ch in "[{":
                    depth += 1
                elif ch in "]}":
                    depth = max(0, depth - 1)
                elif ch == "," and depth == 0:
                    part = "".join(buf).strip()
                    if part:
                        parts.append(part)
                    buf = []
                    i += 1
                    continue
            buf.append(ch)
            i += 1
        tail = "".join(buf).strip()
        if tail:
            parts.append(tail)
        return parts

    def parse_value(v: str) -> Any:
        v = v.strip()
        if not v:
            return ""
        if v.startswith("[") and v.endswith("]"):
            inner = v[1:-1].strip()
            if not inner:
                return []
            return [parse_value(item) for item in split_top_level(inner)]
        if v.startswith("{") and v.endswith("}"):
            inner = v[1:-1].strip()
            if not inner:
                return {}
            out: dict[str, Any] = {}
            for item in split_top_level(inner):
                if ":" not in item:
                    continue
                k_str, v_str = item.split(":", 1)
                key = parse_value(k_str)
                if not isinstance(key, str):
                    key = str(key)
                out[key] = parse_value(v_str)
            return out
        if v.lower() in {"true", "false"}:
            return v.lower() == "true"
        try:
            return int(v)
        except ValueError:
            try:
                return float(v)
            except ValueError:
                return v.strip("\"'")

    def parse_args(arg_str: str) -> dict[str, Any]:
        parsed: dict[str, Any] = {}
        for part in split_top_level(arg_str):
            if ":" not in part:
                continue
            key, value = part.split(":", 1)
            key = key.strip()
            parsed[key] = parse_value(value)
        return parsed

    calls = []
    for name, args in re.findall(
        r"<start_function_call>call:(\w+)\{(.*?)\}<end_function_call>",
        text,
        re.DOTALL,
    ):
        parsed_args = parse_args(args)
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


def _load_prompt(prompt_arg: str | None, prompt_file: str | None) -> str:
    if prompt_arg:
        return prompt_arg
    if prompt_file:
        path = Path(prompt_file)
        if not path.exists():
            raise FileNotFoundError(f"Prompt file not found: {path}")
        return path.read_text(encoding="utf-8")
    default_path = Path(__file__).resolve().parent / "agent_prompt.txt"
    if default_path.exists():
        return default_path.read_text(encoding="utf-8")
    raise ValueError("Provide --prompt or --prompt-file (no default prompt found).")


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
    parser.add_argument("--max-new-tokens", type=int, default=128)
    parser.add_argument("--max-turns", type=int, default=4)
    parser.add_argument("--device")
    parser.add_argument("--show-raw", action="store_true")
    parser.add_argument("--lora-path", help="Optional LoRA adapter directory")
    parser.add_argument("--merge-lora", action="store_true", help="Merge LoRA weights into base model")
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

    model = _load_model(model_path, device, args.lora_path, args.merge_lora)

    tools = build_tools()

    prompt = _load_prompt(args.prompt, args.prompt_file)

    messages: list[dict[str, Any]] = [
        {"role": "developer", "content": DEFAULT_SYSTEM_MSG},
        {"role": "user", "content": prompt},
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
