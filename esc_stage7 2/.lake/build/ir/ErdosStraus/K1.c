// Lean compiler output
// Module: ErdosStraus.K1
// Imports: Init Mathlib ErdosStraus.K0
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
LEAN_EXPORT lean_object* l_ErdosStraus_x1(lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_x1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_negMod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_m1;
LEAN_EXPORT lean_object* l_ErdosStraus_negMod___boxed(lean_object*, lean_object*);
lean_object* l_ErdosStraus_x0(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_x1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_ErdosStraus_x0(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_x1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ErdosStraus_x1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_ErdosStraus_m1() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(7u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_negMod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_nat_mod(x_2, x_1);
x_4 = lean_nat_sub(x_1, x_3);
lean_dec(x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_negMod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ErdosStraus_negMod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_K0(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ErdosStraus_K1(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ErdosStraus_K0(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ErdosStraus_m1 = _init_l_ErdosStraus_m1();
lean_mark_persistent(l_ErdosStraus_m1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
