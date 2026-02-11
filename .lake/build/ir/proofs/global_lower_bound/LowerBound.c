// Lean compiler output
// Module: proofs.global_lower_bound.LowerBound
// Imports: public import Init public import proofs.global_lower_bound.LowerBound.Defs public import proofs.global_lower_bound.LowerBound.TraceEq public import proofs.global_lower_bound.LowerBound.Specs public import proofs.global_lower_bound.LowerBound.Adversary public import proofs.global_lower_bound.LowerBound.ValuesLB public import proofs.global_lower_bound.LowerBound.MachineTraceEq public import proofs.global_lower_bound.LowerBound.CycleLB public import proofs.global_lower_bound.LowerBound.EngineMixLB public import proofs.global_lower_bound.LowerBound.EngineMixKernel public import proofs.global_lower_bound.LowerBound.EngineMixMemBig public import proofs.global_lower_bound.LowerBound.LowerBounds public import proofs.global_lower_bound.LowerBound.MemBigRoundDistinct
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Defs(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_TraceEq(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Specs(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Adversary(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_ValuesLB(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MachineTraceEq(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_CycleLB(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_EngineMixLB(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_EngineMixKernel(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_EngineMixMemBig(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_LowerBounds(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MemBigRoundDistinct(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_TraceEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Specs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Adversary(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_ValuesLB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MachineTraceEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_CycleLB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_EngineMixLB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_EngineMixKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_EngineMixMemBig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_LowerBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MemBigRoundDistinct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
