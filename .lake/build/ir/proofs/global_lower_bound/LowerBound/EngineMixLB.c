// Lean compiler output
// Module: proofs.global_lower_bound.LowerBound.EngineMixLB
// Imports: public import Init public import proofs.global_lower_bound.LowerBound.MachineTraceEq
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
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgram___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome___private_proofs_global__lower__bound_LowerBound_EngineMixLB_0__ProofGlobalLowerBound_engineCountsOfProgramList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineLowerBound(lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_loadStoreLowerBound(lean_object*, lean_object*);
lean_object* lp_original__performance__takehome_ProofCommon_ceilDiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgram(lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___boxed(lean_object*);
static lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___closed__0;
LEAN_EXPORT lean_object* lp_original__performance__takehome___private_proofs_global__lower__bound_LowerBound_EngineMixLB_0__ProofGlobalLowerBound_engineCountsOfProgramList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_loadStoreLowerBound___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineLowerBound(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_22; uint8_t x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_unsigned_to_nat(6u);
x_8 = lp_original__performance__takehome_ProofCommon_ceilDiv(x_2, x_7);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(12u);
x_13 = lp_original__performance__takehome_ProofCommon_ceilDiv(x_3, x_12);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lp_original__performance__takehome_ProofCommon_ceilDiv(x_4, x_17);
lean_dec(x_4);
x_22 = lp_original__performance__takehome_ProofCommon_ceilDiv(x_6, x_17);
lean_dec(x_6);
x_23 = lean_nat_dec_le(x_5, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
x_19 = x_5;
goto block_21;
}
else
{
lean_dec(x_5);
x_19 = x_22;
goto block_21;
}
block_11:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
return x_8;
}
else
{
lean_dec(x_8);
return x_9;
}
}
block_16:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
x_9 = x_13;
goto block_11;
}
else
{
lean_dec(x_13);
x_9 = x_14;
goto block_11;
}
}
block_21:
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
x_14 = x_18;
goto block_16;
}
else
{
lean_dec(x_18);
x_14 = x_19;
goto block_16;
}
}
}
}
static lean_object* _init_lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___closed__0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = l_List_lengthTR___redArg(x_6);
x_18 = lean_nat_add(x_17, x_12);
lean_dec(x_12);
lean_dec(x_17);
x_19 = l_List_lengthTR___redArg(x_5);
x_20 = lean_nat_add(x_19, x_13);
lean_dec(x_13);
lean_dec(x_19);
x_21 = l_List_lengthTR___redArg(x_7);
x_22 = lean_nat_add(x_21, x_14);
lean_dec(x_14);
lean_dec(x_21);
x_23 = l_List_lengthTR___redArg(x_9);
x_24 = lean_nat_add(x_23, x_15);
lean_dec(x_15);
lean_dec(x_23);
x_25 = l_List_lengthTR___redArg(x_8);
x_26 = lean_nat_add(x_25, x_16);
lean_dec(x_16);
lean_dec(x_25);
lean_ctor_set(x_10, 4, x_26);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_22);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
x_29 = lean_ctor_get(x_10, 2);
x_30 = lean_ctor_get(x_10, 3);
x_31 = lean_ctor_get(x_10, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_32 = l_List_lengthTR___redArg(x_6);
x_33 = lean_nat_add(x_32, x_27);
lean_dec(x_27);
lean_dec(x_32);
x_34 = l_List_lengthTR___redArg(x_5);
x_35 = lean_nat_add(x_34, x_28);
lean_dec(x_28);
lean_dec(x_34);
x_36 = l_List_lengthTR___redArg(x_7);
x_37 = lean_nat_add(x_36, x_29);
lean_dec(x_29);
lean_dec(x_36);
x_38 = l_List_lengthTR___redArg(x_9);
x_39 = lean_nat_add(x_38, x_30);
lean_dec(x_30);
lean_dec(x_38);
x_40 = l_List_lengthTR___redArg(x_8);
x_41 = lean_nat_add(x_40, x_31);
lean_dec(x_31);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgram(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgram___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgram(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome___private_proofs_global__lower__bound_LowerBound_EngineMixLB_0__ProofGlobalLowerBound_engineCountsOfProgramList_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome___private_proofs_global__lower__bound_LowerBound_EngineMixLB_0__ProofGlobalLowerBound_engineCountsOfProgramList_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_original__performance__takehome___private_proofs_global__lower__bound_LowerBound_EngineMixLB_0__ProofGlobalLowerBound_engineCountsOfProgramList_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_loadStoreLowerBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lp_original__performance__takehome_ProofCommon_ceilDiv(x_1, x_3);
x_5 = lp_original__performance__takehome_ProofCommon_ceilDiv(x_2, x_3);
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_original__performance__takehome_ProofGlobalLowerBound_loadStoreLowerBound___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_original__performance__takehome_ProofGlobalLowerBound_loadStoreLowerBound(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MachineTraceEq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_EngineMixLB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_original__performance__takehome_proofs_global__lower__bound_LowerBound_MachineTraceEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___closed__0 = _init_lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___closed__0();
lean_mark_persistent(lp_original__performance__takehome_ProofGlobalLowerBound_engineCountsOfProgramList___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
