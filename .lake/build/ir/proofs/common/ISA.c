// Lean compiler output
// Module: proofs.common.ISA
// Imports: public import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_HEIGHT;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_STORE__CAP;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_BATCH__SIZE;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_SCRATCH__SIZE;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_ALU__CAP;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_LANES;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_VECTORS;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_N__NODES;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_VALU__CAP;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_MOD32;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_VLEN;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_ROUNDS;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_LOAD__CAP;
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofISA_FLOW__CAP;
static lean_object* _init_lp_original__performance__takehome_ProofISA_VLEN() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(8u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_MOD32() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("4294967296");
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_VALU__CAP() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(6u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_ALU__CAP() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(12u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_LOAD__CAP() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_STORE__CAP() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_FLOW__CAP() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_SCRATCH__SIZE() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1536u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_ROUNDS() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(16u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_VECTORS() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(32u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_LANES() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(256u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_HEIGHT() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(10u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_N__NODES() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2047u);
return x_1;
}
}
static lean_object* _init_lp_original__performance__takehome_ProofISA_BATCH__SIZE() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(256u);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_original__performance__takehome_proofs_common_ISA(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_original__performance__takehome_ProofISA_VLEN = _init_lp_original__performance__takehome_ProofISA_VLEN();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_VLEN);
lp_original__performance__takehome_ProofISA_MOD32 = _init_lp_original__performance__takehome_ProofISA_MOD32();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_MOD32);
lp_original__performance__takehome_ProofISA_VALU__CAP = _init_lp_original__performance__takehome_ProofISA_VALU__CAP();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_VALU__CAP);
lp_original__performance__takehome_ProofISA_ALU__CAP = _init_lp_original__performance__takehome_ProofISA_ALU__CAP();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_ALU__CAP);
lp_original__performance__takehome_ProofISA_LOAD__CAP = _init_lp_original__performance__takehome_ProofISA_LOAD__CAP();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_LOAD__CAP);
lp_original__performance__takehome_ProofISA_STORE__CAP = _init_lp_original__performance__takehome_ProofISA_STORE__CAP();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_STORE__CAP);
lp_original__performance__takehome_ProofISA_FLOW__CAP = _init_lp_original__performance__takehome_ProofISA_FLOW__CAP();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_FLOW__CAP);
lp_original__performance__takehome_ProofISA_SCRATCH__SIZE = _init_lp_original__performance__takehome_ProofISA_SCRATCH__SIZE();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_SCRATCH__SIZE);
lp_original__performance__takehome_ProofISA_ROUNDS = _init_lp_original__performance__takehome_ProofISA_ROUNDS();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_ROUNDS);
lp_original__performance__takehome_ProofISA_VECTORS = _init_lp_original__performance__takehome_ProofISA_VECTORS();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_VECTORS);
lp_original__performance__takehome_ProofISA_LANES = _init_lp_original__performance__takehome_ProofISA_LANES();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_LANES);
lp_original__performance__takehome_ProofISA_HEIGHT = _init_lp_original__performance__takehome_ProofISA_HEIGHT();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_HEIGHT);
lp_original__performance__takehome_ProofISA_N__NODES = _init_lp_original__performance__takehome_ProofISA_N__NODES();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_N__NODES);
lp_original__performance__takehome_ProofISA_BATCH__SIZE = _init_lp_original__performance__takehome_ProofISA_BATCH__SIZE();
lean_mark_persistent(lp_original__performance__takehome_ProofISA_BATCH__SIZE);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
