// Lean compiler output
// Module: ErdosStraus.TenKObstruction
// Imports: Init Mathlib ErdosStraus.Covering ErdosStraus.FamiliesK10Common ErdosStraus.QRCommon
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
static lean_object* l_ErdosStraus_K10List___closed__10;
static lean_object* l_ErdosStraus_K10List___closed__5;
static lean_object* l_ErdosStraus_K10List___closed__9;
static lean_object* l_ErdosStraus_K10List___closed__6;
static lean_object* l_ErdosStraus_K10List___closed__8;
static lean_object* l_ErdosStraus_K10List___closed__7;
static lean_object* l_ErdosStraus_K10List___closed__4;
LEAN_EXPORT lean_object* l_ErdosStraus_K10List;
static lean_object* l_ErdosStraus_K10List___closed__2;
static lean_object* l_ErdosStraus_K10List___closed__1;
static lean_object* l_ErdosStraus_K10List___closed__3;
static lean_object* _init_l_ErdosStraus_K10List___closed__1() {
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
static lean_object* _init_l_ErdosStraus_K10List___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = l_ErdosStraus_K10List___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = l_ErdosStraus_K10List___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = l_ErdosStraus_K10List___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(17u);
x_2 = l_ErdosStraus_K10List___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = l_ErdosStraus_K10List___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = l_ErdosStraus_K10List___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = l_ErdosStraus_K10List___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_ErdosStraus_K10List___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_ErdosStraus_K10List___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ErdosStraus_K10List() {
_start:
{
lean_object* x_1; 
x_1 = l_ErdosStraus_K10List___closed__10;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Covering(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_FamiliesK10Common(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_QRCommon(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ErdosStraus_TenKObstruction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_Covering(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_FamiliesK10Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_QRCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ErdosStraus_K10List___closed__1 = _init_l_ErdosStraus_K10List___closed__1();
lean_mark_persistent(l_ErdosStraus_K10List___closed__1);
l_ErdosStraus_K10List___closed__2 = _init_l_ErdosStraus_K10List___closed__2();
lean_mark_persistent(l_ErdosStraus_K10List___closed__2);
l_ErdosStraus_K10List___closed__3 = _init_l_ErdosStraus_K10List___closed__3();
lean_mark_persistent(l_ErdosStraus_K10List___closed__3);
l_ErdosStraus_K10List___closed__4 = _init_l_ErdosStraus_K10List___closed__4();
lean_mark_persistent(l_ErdosStraus_K10List___closed__4);
l_ErdosStraus_K10List___closed__5 = _init_l_ErdosStraus_K10List___closed__5();
lean_mark_persistent(l_ErdosStraus_K10List___closed__5);
l_ErdosStraus_K10List___closed__6 = _init_l_ErdosStraus_K10List___closed__6();
lean_mark_persistent(l_ErdosStraus_K10List___closed__6);
l_ErdosStraus_K10List___closed__7 = _init_l_ErdosStraus_K10List___closed__7();
lean_mark_persistent(l_ErdosStraus_K10List___closed__7);
l_ErdosStraus_K10List___closed__8 = _init_l_ErdosStraus_K10List___closed__8();
lean_mark_persistent(l_ErdosStraus_K10List___closed__8);
l_ErdosStraus_K10List___closed__9 = _init_l_ErdosStraus_K10List___closed__9();
lean_mark_persistent(l_ErdosStraus_K10List___closed__9);
l_ErdosStraus_K10List___closed__10 = _init_l_ErdosStraus_K10List___closed__10();
lean_mark_persistent(l_ErdosStraus_K10List___closed__10);
l_ErdosStraus_K10List = _init_l_ErdosStraus_K10List();
lean_mark_persistent(l_ErdosStraus_K10List);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
