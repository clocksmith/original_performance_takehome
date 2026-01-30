from perf_takehome import KernelBuilder as BaseKernelBuilder
from generator.autogen_eq_5 import build_instrs


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(
        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int
    ):
        self.instrs = build_instrs()
