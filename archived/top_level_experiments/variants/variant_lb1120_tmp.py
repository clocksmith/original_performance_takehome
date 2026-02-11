from __future__ import annotations
import json
from dataclasses import replace
from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

with open('tmp/spec_lb1120.json','r',encoding='utf-8') as f:
    SPEC_DICT = json.load(f)['spec']
SPEC_LB1120 = replace(SPEC_BASE, **SPEC_DICT)

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_LB1120)
