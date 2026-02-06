"""
Template for external kernel builders.
Subclass the original KernelBuilder and only override build_kernel().
"""

from perf_takehome import KernelBuilder as BaseKernelBuilder


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(
        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int
    ):
        # TODO: implement kernel construction
        raise NotImplementedError("TODO: implement build_kernel")
