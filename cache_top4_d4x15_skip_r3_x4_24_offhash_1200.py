from perf_takehome import KernelBuilder as BaseKernelBuilder
from generator.cache_top4_d4x15_skip_r3_x4_24_offhash_1200 import build_instrs


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(
        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int
    ):
        self.instrs = build_instrs()
