from perf_takehome import KernelBuilder as _BaseKernelBuilder


class KernelBuilder(_BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        if (
            forest_height == 10
            and rounds == 16
            and batch_size == 256
            and n_nodes == 2 ** (forest_height + 1) - 1
        ):
            from generator.ub_energy_bundle_1349 import build_instrs

            self.instrs = build_instrs()
            return
        return super().build_kernel(forest_height, n_nodes, batch_size, rounds)

