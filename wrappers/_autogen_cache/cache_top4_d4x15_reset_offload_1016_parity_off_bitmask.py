from perf_takehome import KernelBuilder as BaseKernelBuilder
from generator.cache_top4_d4x15_reset_offload_1016_parity_off_bitmask import build_instrs


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(
        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int
    ):
        self.instrs = build_instrs()
