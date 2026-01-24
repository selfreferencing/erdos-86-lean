// Lean compiler output
// Module: ErdosStraus.K0
// Imports: Init Mathlib ErdosStraus.Basic ErdosStraus.Bradford
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
LEAN_EXPORT lean_object* l_ErdosStraus_m0;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_x0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_x0(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_x0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_div(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_x0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ErdosStraus_x0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_ErdosStraus_m0() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Bradford(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ErdosStraus_K0(uint8_t builtin, lean_object* w) {
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
l_ErdosStraus_m0 = _init_l_ErdosStraus_m0();
lean_mark_persistent(l_ErdosStraus_m0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
