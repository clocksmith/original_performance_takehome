
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.op_list import build_ops
from generator.scratch_layout import build_layout, ScratchAlloc
from generator.offload import apply_offload_stream

spec = SPEC_UB_ENERGY_BUNDLE_1291
scratch = ScratchAlloc()
layout = build_layout(spec, scratch)
pre = build_ops(spec, layout)
ordered_ops = []
build_ops(spec, layout, ordered_ops=ordered_ops)

print(f"Total VALU (pre-offload): {len(pre.valu_ops)}")
print(f"Total ALU (pre-offload): {len(pre.alu_ops)}")
print(f"Total Flow (pre-offload): {len(pre.flow_ops)}")
print(f"Total Load (pre-offload): {len(pre.load_ops)}")
print(f"Total Store (pre-offload): {len(pre.store_ops)}")

final_ops = apply_offload_stream(spec, ordered_ops)
from collections import Counter
cnt = Counter(op.engine for op in final_ops)
print("\nPost-offload:")
print(f"VALU: {cnt['valu']}")
print(f"ALU: {cnt['alu']}")
print(f"Flow: {cnt['flow']}")
print(f"Load: {cnt['load']}")
print(f"Store: {cnt['store']}")

cycles = 1291
print(f"\nUtilization at {cycles} cycles:")
print(f"VALU: {cnt['valu'] / (cycles * 6):.2%}")
print(f"ALU: {cnt['alu'] / (cycles * 12):.2%}")
print(f"Flow: {cnt['flow'] / (cycles * 1):.2%}")
print(f"Load: {cnt['load'] / (cycles * 2):.2%}")
print(f"Store: {cnt['store'] / (cycles * 2):.2%}")
