// Lean compiler output
// Module: ErdosStraus.CoveringUnbounded
// Imports: Init Mathlib ErdosStraus.Basic ErdosStraus.Bradford ErdosStraus.Covering ErdosStraus.Families_k5 ErdosStraus.Families_k7 ErdosStraus.Families_k9 ErdosStraus.Families_k11 ErdosStraus.Families_k14 ErdosStraus.Families_k17 ErdosStraus.Families_k19 ErdosStraus.Families_k23 ErdosStraus.Families_k26 ErdosStraus.Families_k29 ErdosStraus.QRCommon ErdosStraus.TenKObstruction
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
LEAN_EXPORT lean_object* l_ErdosStraus_K10;
LEAN_EXPORT lean_object* l_Multiset_filter___at_ErdosStraus_MordellHardResiduesM___spec__2(lean_object*);
static lean_object* l_ErdosStraus_K10___closed__3;
LEAN_EXPORT lean_object* l_Finset_filter___at_ErdosStraus_MordellHardResiduesM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_coveringK___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_M;
static lean_object* l_ErdosStraus_K10___closed__10;
static lean_object* l_ErdosStraus_K10___closed__8;
lean_object* l_List_range(lean_object*);
uint8_t l_List_elem___at_Lean_Meta_Occurrences_contains___spec__1(lean_object*, lean_object*);
static lean_object* l_ErdosStraus_K10___closed__7;
uint8_t l_Multiset_decidableMem___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_ErdosStraus_K10___closed__9;
static lean_object* l_ErdosStraus_K10___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3(lean_object*, lean_object*);
static lean_object* l_ErdosStraus_MordellHardResiduesM___closed__1;
static lean_object* l_ErdosStraus_K10___closed__6;
static lean_object* l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3___closed__1;
LEAN_EXPORT lean_object* l_ErdosStraus_MordellHardResiduesM;
static lean_object* l_ErdosStraus_K10___closed__4;
LEAN_EXPORT lean_object* l_ErdosStraus_coveringK(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_ErdosStraus_K10___closed__1;
LEAN_EXPORT lean_object* l_ErdosStraus_MordellHardResidues840;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
static lean_object* l_ErdosStraus_K10___closed__5;
static lean_object* l_ErdosStraus_MordellHardResidues840___closed__1;
static lean_object* _init_l_ErdosStraus_M() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("4185369236605294920");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at_Lean_Meta_Occurrences_contains___spec__1(x_1, x_2);
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
static lean_object* _init_l_ErdosStraus_MordellHardResidues840___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(529u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_MordellHardResidues840() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_unsigned_to_nat(361u);
x_2 = l_ErdosStraus_MordellHardResidues840___closed__1;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
x_4 = lean_unsigned_to_nat(289u);
x_5 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_4, x_3);
x_6 = lean_unsigned_to_nat(169u);
x_7 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_6, x_5);
x_8 = lean_unsigned_to_nat(121u);
x_9 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_10, x_9);
return x_11;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__1() {
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
static lean_object* _init_l_ErdosStraus_K10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = l_ErdosStraus_K10___closed__1;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = l_ErdosStraus_K10___closed__2;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = l_ErdosStraus_K10___closed__3;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(17u);
x_2 = l_ErdosStraus_K10___closed__4;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = l_ErdosStraus_K10___closed__5;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = l_ErdosStraus_K10___closed__6;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = l_ErdosStraus_K10___closed__7;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_ErdosStraus_K10___closed__8;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_ErdosStraus_K10___closed__9;
x_3 = l_Multiset_ndinsert___at_ErdosStraus_MordellHardResidues840___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10() {
_start:
{
lean_object* x_1; 
x_1 = l_ErdosStraus_K10___closed__10;
return x_1;
}
}
static lean_object* _init_l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(840u);
x_8 = lean_nat_mod(x_5, x_7);
x_9 = l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3___closed__1;
x_10 = l_ErdosStraus_MordellHardResidues840;
x_11 = l_Multiset_decidableMem___rarg(x_9, x_8, x_10);
if (x_11 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(840u);
x_17 = lean_nat_mod(x_14, x_16);
x_18 = l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3___closed__1;
x_19 = l_ErdosStraus_MordellHardResidues840;
x_20 = l_Multiset_decidableMem___rarg(x_18, x_17, x_19);
if (x_20 == 0)
{
lean_dec(x_14);
x_1 = x_15;
goto _start;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_15;
x_2 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Multiset_filter___at_ErdosStraus_MordellHardResiduesM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Finset_filter___at_ErdosStraus_MordellHardResiduesM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Multiset_filter___at_ErdosStraus_MordellHardResiduesM___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_ErdosStraus_MordellHardResiduesM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ErdosStraus_M;
x_2 = l_List_range(x_1);
return x_2;
}
}
static lean_object* _init_l_ErdosStraus_MordellHardResiduesM() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ErdosStraus_MordellHardResiduesM___closed__1;
x_2 = l_Multiset_filter___at_ErdosStraus_MordellHardResiduesM___spec__2(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_coveringK(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(5u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_coveringK___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ErdosStraus_coveringK(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Bradford(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Covering(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k5(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k7(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k9(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k11(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k14(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k17(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k19(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k23(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k26(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Families__k29(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_QRCommon(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_TenKObstruction(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ErdosStraus_CoveringUnbounded(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Bradford(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Covering(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k5(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k7(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k9(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k11(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k14(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k17(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k19(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k23(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k26(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Families__k29(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_QRCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_TenKObstruction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ErdosStraus_M = _init_l_ErdosStraus_M();
lean_mark_persistent(l_ErdosStraus_M);
l_ErdosStraus_MordellHardResidues840___closed__1 = _init_l_ErdosStraus_MordellHardResidues840___closed__1();
lean_mark_persistent(l_ErdosStraus_MordellHardResidues840___closed__1);
l_ErdosStraus_MordellHardResidues840 = _init_l_ErdosStraus_MordellHardResidues840();
lean_mark_persistent(l_ErdosStraus_MordellHardResidues840);
l_ErdosStraus_K10___closed__1 = _init_l_ErdosStraus_K10___closed__1();
lean_mark_persistent(l_ErdosStraus_K10___closed__1);
l_ErdosStraus_K10___closed__2 = _init_l_ErdosStraus_K10___closed__2();
lean_mark_persistent(l_ErdosStraus_K10___closed__2);
l_ErdosStraus_K10___closed__3 = _init_l_ErdosStraus_K10___closed__3();
lean_mark_persistent(l_ErdosStraus_K10___closed__3);
l_ErdosStraus_K10___closed__4 = _init_l_ErdosStraus_K10___closed__4();
lean_mark_persistent(l_ErdosStraus_K10___closed__4);
l_ErdosStraus_K10___closed__5 = _init_l_ErdosStraus_K10___closed__5();
lean_mark_persistent(l_ErdosStraus_K10___closed__5);
l_ErdosStraus_K10___closed__6 = _init_l_ErdosStraus_K10___closed__6();
lean_mark_persistent(l_ErdosStraus_K10___closed__6);
l_ErdosStraus_K10___closed__7 = _init_l_ErdosStraus_K10___closed__7();
lean_mark_persistent(l_ErdosStraus_K10___closed__7);
l_ErdosStraus_K10___closed__8 = _init_l_ErdosStraus_K10___closed__8();
lean_mark_persistent(l_ErdosStraus_K10___closed__8);
l_ErdosStraus_K10___closed__9 = _init_l_ErdosStraus_K10___closed__9();
lean_mark_persistent(l_ErdosStraus_K10___closed__9);
l_ErdosStraus_K10___closed__10 = _init_l_ErdosStraus_K10___closed__10();
lean_mark_persistent(l_ErdosStraus_K10___closed__10);
l_ErdosStraus_K10 = _init_l_ErdosStraus_K10();
lean_mark_persistent(l_ErdosStraus_K10);
l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3___closed__1 = _init_l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3___closed__1();
lean_mark_persistent(l_List_filterTR_loop___at_ErdosStraus_MordellHardResiduesM___spec__3___closed__1);
l_ErdosStraus_MordellHardResiduesM___closed__1 = _init_l_ErdosStraus_MordellHardResiduesM___closed__1();
lean_mark_persistent(l_ErdosStraus_MordellHardResiduesM___closed__1);
l_ErdosStraus_MordellHardResiduesM = _init_l_ErdosStraus_MordellHardResiduesM();
lean_mark_persistent(l_ErdosStraus_MordellHardResiduesM);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
