import os, sys, inspect

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
parentdir = os.path.dirname(currentdir)
sys.path.insert(0, parentdir)
sys.path.insert(0, currentdir)

from functools import lru_cache
import subprocess
import unittest
import random

from frozen_problem import (
    Machine,
    build_mem_image,
    reference_kernel2,
    Tree,
    Input,
    N_CORES,
    VLEN,
)
from perf_takehome import KernelBuilder


@lru_cache(maxsize=None)
def kernel_builder(forest_height: int, n_nodes: int, batch_size: int, rounds: int):
    kb = KernelBuilder()
    kb.build_kernel(forest_height, n_nodes, batch_size, rounds)
    return kb


def do_kernel_test(forest_height: int, rounds: int, batch_size: int, check_indices: bool = True):
    tag = "VALUES+INDICES" if check_indices else "VALUES_ONLY"
    print(f"Testing {tag} {forest_height=}, {rounds=}, {batch_size=}")
    # Note the random generator is not seeded here
    forest = Tree.generate(forest_height)
    inp = Input.generate(forest, batch_size, rounds)
    mem = build_mem_image(forest, inp)

    kb = kernel_builder(forest.height, len(forest.values), len(inp.indices), rounds)

    machine = Machine(mem, kb.instrs, kb.debug_info(), n_cores=N_CORES)
    machine.enable_pause = False
    machine.enable_debug = False
    machine.run()

    for ref_mem in reference_kernel2(mem):
        pass

    inp_values_p = ref_mem[6]
    assert (
        machine.mem[inp_values_p : inp_values_p + len(inp.values)]
        == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
    ), "Incorrect output values"
    if check_indices:
        inp_indices_p = ref_mem[5]
        assert (
            machine.mem[inp_indices_p : inp_indices_p + len(inp.indices)]
            == ref_mem[inp_indices_p : inp_indices_p + len(inp.indices)]
        ), "Incorrect output indices"
    print("CYCLES: ", machine.cycle)
    return machine.cycle


def do_kernel_test_inline(forest_height: int, rounds: int, batch_size: int, check_indices: bool = True):
    tag = "VALUES+INDICES" if check_indices else "VALUES_ONLY"
    print(f"Testing INLINE {tag} {forest_height=}, {rounds=}, {batch_size=}")
    forest = Tree.generate(forest_height)
    inp = Input.generate(forest, batch_size, rounds)

    kb = kernel_builder(forest.height, len(forest.values), len(inp.indices), rounds)

    # Build mem inline so it's not bound to a local at debug_info call
    machine = Machine(build_mem_image(forest, inp), kb.instrs, kb.debug_info(), n_cores=N_CORES)
    machine.enable_pause = False
    machine.enable_debug = False
    machine.run()

    ref_mem = build_mem_image(forest, inp)
    for ref_mem in reference_kernel2(ref_mem):
        pass

    inp_values_p = ref_mem[6]
    assert (
        machine.mem[inp_values_p : inp_values_p + len(inp.values)]
        == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
    ), "Incorrect output values"
    if check_indices:
        inp_indices_p = ref_mem[5]
        assert (
            machine.mem[inp_indices_p : inp_indices_p + len(inp.indices)]
            == ref_mem[inp_indices_p : inp_indices_p + len(inp.indices)]
        ), "Incorrect output indices"
    print("CYCLES: ", machine.cycle)
    return machine.cycle


def do_kernel_test_no_mem_at_debug(forest_height: int, rounds: int, batch_size: int, check_indices: bool = True):
    tag = "VALUES+INDICES" if check_indices else "VALUES_ONLY"
    print(f"Testing NO_MEM_AT_DEBUG {tag} {forest_height=}, {rounds=}, {batch_size=}")
    forest = Tree.generate(forest_height)
    inp = Input.generate(forest, batch_size, rounds)

    kb = kernel_builder(forest.height, len(forest.values), len(inp.indices), rounds)
    dbg = kb.debug_info()  # call before any mem exists

    machine = Machine(build_mem_image(forest, inp), kb.instrs, dbg, n_cores=N_CORES)
    machine.enable_pause = False
    machine.enable_debug = False
    machine.run()

    ref_mem = build_mem_image(forest, inp)
    for ref_mem in reference_kernel2(ref_mem):
        pass

    inp_values_p = ref_mem[6]
    assert (
        machine.mem[inp_values_p : inp_values_p + len(inp.values)]
        == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
    ), "Incorrect output values"
    if check_indices:
        inp_indices_p = ref_mem[5]
        assert (
            machine.mem[inp_indices_p : inp_indices_p + len(inp.indices)]
            == ref_mem[inp_indices_p : inp_indices_p + len(inp.indices)]
        ), "Incorrect output indices"
    print("CYCLES: ", machine.cycle)
    return machine.cycle


def do_kernel_test_multi_mem_same_shape(
    forest_height: int, rounds: int, batch_size: int, check_indices: bool = True
):
    tag = "VALUES+INDICES" if check_indices else "VALUES_ONLY"
    print(f"Testing MULTI_MEM {tag} {forest_height=}, {rounds=}, {batch_size=}")
    forest = Tree.generate(forest_height)
    inp = Input.generate(forest, batch_size, rounds)

    # Create extra same-shape mems to simulate multiple candidates in GC
    extra = []
    for _ in range(3):
        f2 = Tree.generate(forest_height)
        i2 = Input.generate(f2, batch_size, rounds)
        extra.append((f2, i2, build_mem_image(f2, i2)))

    kb = kernel_builder(forest.height, len(forest.values), len(inp.indices), rounds)

    mem = build_mem_image(forest, inp)
    machine = Machine(mem, kb.instrs, kb.debug_info(), n_cores=N_CORES)
    machine.enable_pause = False
    machine.enable_debug = False
    machine.run()

    for ref_mem in reference_kernel2(mem):
        pass

    inp_values_p = ref_mem[6]
    assert (
        machine.mem[inp_values_p : inp_values_p + len(inp.values)]
        == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
    ), "Incorrect output values"
    if check_indices:
        inp_indices_p = ref_mem[5]
        assert (
            machine.mem[inp_indices_p : inp_indices_p + len(inp.indices)]
            == ref_mem[inp_indices_p : inp_indices_p + len(inp.indices)]
        ), "Incorrect output indices"
    print("CYCLES: ", machine.cycle)
    return machine.cycle


SINGLE_DISPATCH = {
    "do_kernel_test_values_only": lambda h, r, b: do_kernel_test(
        h, r, b, check_indices=False
    ),
    "do_kernel_test": do_kernel_test,
    "do_kernel_test_inline_values_only": lambda h, r, b: do_kernel_test_inline(
        h, r, b, check_indices=False
    ),
    "do_kernel_test_inline": do_kernel_test_inline,
    "do_kernel_test_no_mem_values_only": lambda h, r, b: do_kernel_test_no_mem_at_debug(
        h, r, b, check_indices=False
    ),
    "do_kernel_test_no_mem": do_kernel_test_no_mem_at_debug,
    "do_kernel_test_multi_mem_values_only": lambda h, r, b: do_kernel_test_multi_mem_same_shape(
        h, r, b, check_indices=False
    ),
    "do_kernel_test_multi_mem": do_kernel_test_multi_mem_same_shape,
}

# Expanded grid within bounds: depths 8-10, rounds 8/10/12/16/20, batch 128-256 (VLEN-aligned)
CASES = [
    (h, r, b)
    for h in (8, 9, 10)
    for r in (8, 10, 12, 16, 20)
    for b in (128, 160, 192, 224, 256)
]

PROBE_SHUFFLE = True
PROBE_SUBPROCESS = True
PROBE_CLUSTER_SIZE = 8
PROBE_CLUSTER_SEED = 1337


BASELINE = 147734
SPEED_CASE = (10, 16, 256)


def _cluster_cases(cases):
    rng = random.Random(PROBE_CLUSTER_SEED)
    out = list(cases)
    rng.shuffle(out)
    clusters = [
        out[i : i + PROBE_CLUSTER_SIZE]
        for i in range(0, len(out), PROBE_CLUSTER_SIZE)
    ]
    rng.shuffle(clusters)
    return clusters


def run_permuted_cases(fn, name: str | None = None):
    if name is None:
        for k, v in SINGLE_DISPATCH.items():
            if v is fn:
                name = k
                break
    if name is None:
        name = fn.__name__
    if PROBE_SUBPROCESS:
        clusters = _cluster_cases(CASES)
        for cluster in clusters:
            args = [
                sys.executable,
                os.path.join(currentdir, "order_probe.py"),
                "--cluster",
                name,
            ]
            for h, r, b in cluster:
                args.extend([str(h), str(r), str(b)])
            subprocess.run(args, check=True)
        return
    cases = list(CASES)
    if PROBE_SHUFFLE:
        random.shuffle(cases)
    for h, r, b in cases:
        fn(h, r, b)


def run_speed_case():
    h, r, b = SPEED_CASE
    res = do_kernel_test(h, r, b)
    print("Speedup over baseline: ", BASELINE / res)


def run_suite_order(names, label):
    print(f"Running {label}: {names}")
    loader = unittest.defaultTestLoader
    suite = unittest.TestSuite()
    for name in names:
        suite.addTests(loader.loadTestsFromName(name))
    runner = unittest.TextTestRunner()
    result = runner.run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)


class CorrectnessTests(unittest.TestCase):
    def test_kernel_correctness(self):
        for _ in range(8):
            do_kernel_test(10, 16, 256)


if __name__ == "__main__":
    if len(sys.argv) >= 6 and sys.argv[1] == "--single":
        h = int(sys.argv[2])
        r = int(sys.argv[3])
        b = int(sys.argv[4])
        name = sys.argv[5]
        fn = SINGLE_DISPATCH.get(name)
        if fn is None:
            raise SystemExit(f"Unknown single fn: {name}")
        fn(h, r, b)
        raise SystemExit(0)
    if len(sys.argv) >= 6 and sys.argv[1] == "--cluster":
        name = sys.argv[2]
        fn = SINGLE_DISPATCH.get(name)
        if fn is None:
            raise SystemExit(f"Unknown cluster fn: {name}")
        vals = sys.argv[3:]
        if len(vals) % 3 != 0:
            raise SystemExit("Cluster args must be triples of h r b")
        for i in range(0, len(vals), 3):
            h = int(vals[i])
            r = int(vals[i + 1])
            b = int(vals[i + 2])
            fn(h, r, b)
        raise SystemExit(0)
    run_permuted_cases(
        SINGLE_DISPATCH["do_kernel_test_values_only"], "do_kernel_test_values_only"
    )
    run_permuted_cases(SINGLE_DISPATCH["do_kernel_test"], "do_kernel_test")
    run_permuted_cases(
        SINGLE_DISPATCH["do_kernel_test_inline_values_only"],
        "do_kernel_test_inline_values_only",
    )
    run_permuted_cases(
        SINGLE_DISPATCH["do_kernel_test_inline"], "do_kernel_test_inline"
    )
    run_permuted_cases(
        SINGLE_DISPATCH["do_kernel_test_no_mem_values_only"],
        "do_kernel_test_no_mem_values_only",
    )
    run_permuted_cases(
        SINGLE_DISPATCH["do_kernel_test_no_mem"], "do_kernel_test_no_mem"
    )
    run_permuted_cases(
        SINGLE_DISPATCH["do_kernel_test_multi_mem_values_only"],
        "do_kernel_test_multi_mem_values_only",
    )
    run_permuted_cases(
        SINGLE_DISPATCH["do_kernel_test_multi_mem"],
        "do_kernel_test_multi_mem",
    )
    run_speed_case()
    run_suite_order(["tests.order_probe.CorrectnessTests"], "OrderProbe Correctness")
    run_suite_order(["tests.submission_tests", "perf_takehome.Tests"], "Order A")
    run_suite_order(["perf_takehome.Tests", "tests.submission_tests"], "Order B")
