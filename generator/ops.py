from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass
class Op:
    engine: str
    slot: tuple[Any, ...]
    offloadable: bool = False
    meta: dict[str, Any] | None = None


@dataclass
class OpLists:
    valu_ops: list[Op]
    flow_ops: list[Op]
    load_ops: list[Op]
    store_ops: list[Op]
