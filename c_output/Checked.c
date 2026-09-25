// Lean compiler output
// Module: RequestProject.WFLang.Checked
// Imports: public import Init public import RequestProject.WFLang.FreeCall public import RequestProject.WFLang.Guarded
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
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_eval(lean_object*, lean_object*);
lean_object* lp_RequestProject_WFLang_Expr_evalWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_WFLang_Ty_default(uint8_t);
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_run___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_WFLang_curryEnv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_run___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_6, x_2);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lp_RequestProject_WFLang_Ty_default(x_3);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lp_RequestProject_WFLang_Checked_Term_run(x_4, x_5, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_run___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = lp_RequestProject_WFLang_Checked_Term_run___lam__0(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
x_8 = lean_box(x_5);
lean_inc_ref(x_1);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(lp_RequestProject_WFLang_Checked_Term_run___lam__0___boxed), 6, 5);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_2);
x_10 = lp_RequestProject_WFLang_Expr_evalWith___redArg(x_1, x_9, x_4, x_3, x_6);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_1(x_2, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___redArg(x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = lp_RequestProject___private_RequestProject_WFLang_Checked_0__WFLang_Checked_Term_run_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_WFLang_Checked_Term_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(lp_RequestProject_WFLang_Checked_Term_run), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lp_RequestProject_WFLang_curryEnv___redArg(x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_WFLang_FreeCall(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_WFLang_Guarded(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_WFLang_Checked(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_WFLang_FreeCall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_WFLang_Guarded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
