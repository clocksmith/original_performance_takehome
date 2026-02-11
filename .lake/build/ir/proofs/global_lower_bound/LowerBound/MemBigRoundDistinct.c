// Lean compiler output
// Module: proofs.global_lower_bound.LowerBound.MemBigRoundDistinct
// Imports: public import Init public import proofs.global_lower_bound.LowerBound.MemBigRoundDistinctHelpers
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
lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel(lean_object*, lean_object*);
extern lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memBig;
LEAN_EXPORT uint8_t lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1;
lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__1___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__1(lean_object*);
uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lp_original__performance__takehome_ProofGlobalLowerBound_memBigForestBump(x_1, x_2);
x_4 = lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel(x_3, x_2);
x_5 = lp_original__performance__takehome_ProofGlobalLowerBound_memBig;
x_6 = lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel(x_5, x_2);
x_7 = lean_nat_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_unsigned_to_nat(256u);
x_4 = l_Nat_decidableForallFin___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__1(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_alloc_closure((void*)(lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1___lam__1___boxed), 1, 0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_Nat_decidableForallFin___redArg(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MemBigRoundDistinctHelpers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MemBigRoundDistinct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MemBigRoundDistinctHelpers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1 = _init_lp_original__performance__takehome_ProofGlobalLowerBound_spec__kernel__memBigForestBump__ne__all___nativeDecide__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
