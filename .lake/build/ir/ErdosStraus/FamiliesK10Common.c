// Lean compiler output
// Module: ErdosStraus.FamiliesK10Common
// Imports: public import Init public import ErdosStraus.Basic public import ErdosStraus.K1 public import Mathlib.Data.Finset.Basic public import Mathlib.Tactic
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
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_K10;
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(lean_object*, lean_object*);
lean_object* lp_erdos__straus__stage5_ErdosStraus_x0(lean_object*);
uint8_t lp_mathlib_List_elem___at___00__private_Mathlib_Tactic_Translate_Core_0__Mathlib_Tactic_Translate_applyReplacementFun_visitApp_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_mK(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_xK___boxed(lean_object*, lean_object*);
static lean_object* lp_erdos__straus__stage5_ErdosStraus_K10___closed__0;
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_mK___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_xK(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lp_mathlib_List_elem___at___00__private_Mathlib_Tactic_Translate_Core_0__Mathlib_Tactic_Translate_applyReplacementFun_visitApp_spec__0(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_lp_erdos__straus__stage5_ErdosStraus_K10___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_erdos__straus__stage5_ErdosStraus_K10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_unsigned_to_nat(9u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = lean_unsigned_to_nat(14u);
x_6 = lean_unsigned_to_nat(17u);
x_7 = lean_unsigned_to_nat(19u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_unsigned_to_nat(26u);
x_10 = lp_erdos__straus__stage5_ErdosStraus_K10___closed__0;
x_11 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_9, x_10);
x_12 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_8, x_11);
x_13 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_7, x_12);
x_14 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_6, x_13);
x_15 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_5, x_14);
x_16 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_4, x_15);
x_17 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_3, x_16);
x_18 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_2, x_17);
x_19 = lp_erdos__straus__stage5_Multiset_ndinsert___at___00ErdosStraus_K10_spec__0(x_1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_mK(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_nat_mul(x_2, x_1);
x_4 = lean_unsigned_to_nat(3u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_mK___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_erdos__straus__stage5_ErdosStraus_mK(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_xK(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_erdos__straus__stage5_ErdosStraus_x0(x_1);
x_4 = lean_nat_add(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_erdos__straus__stage5_ErdosStraus_xK___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_erdos__straus__stage5_ErdosStraus_xK(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_erdos__straus__stage5_ErdosStraus_Basic(uint8_t builtin);
lean_object* initialize_erdos__straus__stage5_ErdosStraus_K1(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_erdos__straus__stage5_ErdosStraus_FamiliesK10Common(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_erdos__straus__stage5_ErdosStraus_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_erdos__straus__stage5_ErdosStraus_K1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_erdos__straus__stage5_ErdosStraus_K10___closed__0 = _init_lp_erdos__straus__stage5_ErdosStraus_K10___closed__0();
lean_mark_persistent(lp_erdos__straus__stage5_ErdosStraus_K10___closed__0);
lp_erdos__straus__stage5_ErdosStraus_K10 = _init_lp_erdos__straus__stage5_ErdosStraus_K10();
lean_mark_persistent(lp_erdos__straus__stage5_ErdosStraus_K10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
