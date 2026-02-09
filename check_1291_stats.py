
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.op_list import build_ops
from generator.scratch_layout import build_layout, ScratchAlloc
from generator.offload import apply_offload

spec = SPEC_UB_ENERGY_BUNDLE_1291
scratch = ScratchAlloc()
layout = build_layout(spec, scratch)
ops = build_ops(spec, layout)

print(f"Total VALU (pre-offload): {len(ops.valu_ops)}")
print(f"Total ALU (pre-offload): {len(ops.alu_ops)}")
print(f"Total Flow (pre-offload): {len(ops.flow_ops)}")
print(f"Total Load (pre-offload): {len(ops.load_ops)}")
print(f"Total Store (pre-offload): {len(ops.store_ops)}")

off = apply_offload(spec, ops)
print("\nPost-offload:")
print(f"VALU: {len(off.valu_ops)}")
print(f"ALU: {len(off.alu_ops)}")
print(f"Flow: {len(off.flow_ops)}")
print(f"Load: {len(off.load_ops)}")
print(f"Store: {len(off.store_ops)}")

cycles = 1291
print(f"\nUtilization at {cycles} cycles:")
print(f"VALU: {len(off.valu_ops) / (cycles * 6):.2%}")
print(f"ALU: {len(off.alu_ops) / (cycles * 12):.2%}")
print(f"Flow: {len(off.flow_ops) / (cycles * 1):.2%}")
print(f"Load: {len(off.load_ops) / (cycles * 2):.2%}")
print(f"Store: {len(off.store_ops) / (cycles * 2):.2%}")
