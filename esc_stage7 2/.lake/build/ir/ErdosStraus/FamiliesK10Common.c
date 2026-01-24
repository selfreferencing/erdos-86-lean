// Lean compiler output
// Module: ErdosStraus.FamiliesK10Common
// Imports: Init Mathlib ErdosStraus.Basic ErdosStraus.Bradford ErdosStraus.Covering
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
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_xOfK(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_xOfK___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_mOfK___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_mOfK(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ErdosStraus_mOfK(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_ErdosStraus_mOfK___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ErdosStraus_mOfK(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_xOfK(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_ErdosStraus_mOfK(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(4u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ErdosStraus_xOfK___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ErdosStraus_xOfK(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Bradford(uint8_t builtin, lean_object*);
lean_object* initialize_ErdosStraus_Covering(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ErdosStraus_FamiliesK10Common(uint8_t builtin, lean_object* w) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
