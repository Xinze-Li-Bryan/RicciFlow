// Lean compiler output
// Module: RicciFlow.RicciCurvature
// Imports: public import Init public import Mathlib.Data.Real.Basic public import RicciFlow.RiemannianManifold
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
LEAN_EXPORT lean_object* l_RicciFlow_MetricVelocity_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instZeroMetricVelocity___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instNegMetricVelocity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instSMulMetricVelocity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instNegMetricVelocity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instZeroMetricVelocity___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instAddMetricVelocity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_MetricVelocity_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instAddMetricVelocity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instZeroMetricVelocity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_instSMulMetricVelocity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_RicciTensor_ctorIdx(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature___redArg(lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_RicciTensor_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RicciFlow_MetricVelocity_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_MetricVelocity_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RicciFlow_MetricVelocity_ctorIdx(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instSMulMetricVelocity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instSMulMetricVelocity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RicciFlow_instSMulMetricVelocity___lam__0), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instZeroMetricVelocity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
return x_4;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instZeroMetricVelocity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RicciFlow_instZeroMetricVelocity___lam__0___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instZeroMetricVelocity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RicciFlow_instZeroMetricVelocity___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instAddMetricVelocity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
x_7 = lean_apply_3(x_2, x_3, x_4, x_5);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instAddMetricVelocity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RicciFlow_instAddMetricVelocity___lam__0), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instNegMetricVelocity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_instNegMetricVelocity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RicciFlow_instNegMetricVelocity___lam__0), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_RicciTensor_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_RicciTensor_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RicciFlow_RicciTensor_ctorIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RicciFlow_scalarCurvature___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_RicciFlow_scalarCurvature___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RicciFlow_scalarCurvature(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_RicciFlow_RiemannianManifold(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RicciFlow_RicciCurvature(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RicciFlow_RiemannianManifold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
