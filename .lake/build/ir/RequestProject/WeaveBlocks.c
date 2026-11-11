// Lean compiler output
// Module: RequestProject.WeaveBlocks
// Imports: public import Init public meta import Init public import RequestProject.WeaveShear
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
lean_object* lp_RequestProject_StickPolyhex_StickTiling_tail(lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_nbr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_flank(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_flank___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_flank(lean_object* v_n_1_, lean_object* v_T_2_, lean_object* v_u_3_, lean_object* v_c_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lp_RequestProject_StickPolyhex_StickTiling_tail(v_n_1_, v_T_2_, v_c_4_);
v___x_6_ = lp_RequestProject_StickPolyhex_nbr(v___x_5_, v_u_3_);
lean_dec_ref(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_flank___boxed(lean_object* v_n_7_, lean_object* v_T_8_, lean_object* v_u_9_, lean_object* v_c_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_RequestProject_StickPolyhex_StickTiling_flank(v_n_7_, v_T_8_, v_u_9_, v_c_10_);
lean_dec(v_u_9_);
lean_dec(v_n_7_);
return v_res_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_WeaveShear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_WeaveBlocks(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_WeaveShear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
