// Lean compiler output
// Module: proofs.global_lower_bound.LowerBound.MemBigRoundDistinctHelpers
// Imports: public import Init public import proofs.global_lower_bound.LowerBound.Adversary
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
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump___boxed(lean_object*, lean_object*);
lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_idxAt(lean_object*, lean_object*);
extern lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memBig;
lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_treeBump(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memUpdate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_treeBump___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_unsigned_to_nat(7u);
x_4 = lp_original__performance__takehome_ProofGlobalLowerBound_idxAt(x_1, x_2);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_4);
x_6 = lp_original__performance__takehome_ProofGlobalLowerBound_memBig;
lean_inc(x_5);
x_7 = lp_original__performance__takehome_ProofGlobalLowerBound_memAt(x_6, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lp_original__performance__takehome_ProofGlobalLowerBound_memUpdate(x_6, x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_treeBump(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump(x_1, x_2);
x_5 = lean_unsigned_to_nat(7u);
x_6 = lean_nat_add(x_5, x_3);
x_7 = lp_original__performance__takehome_ProofGlobalLowerBound_memAt(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_treeBump___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_original__performance__takehome_ProofGlobalLowerBound_treeBump(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Adversary(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MemBigRoundDistinctHelpers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_Adversary(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
