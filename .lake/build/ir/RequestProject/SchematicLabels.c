// Lean compiler output
// Module: RequestProject.SchematicLabels
// Imports: public import Init public meta import Init public import RequestProject.SchematicTiling public import RequestProject.EdgeRules
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_shearCell(lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_cellAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_cellAt___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_cellAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_cellAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_RequestProject_StickPolyhex_cellAt___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_cellAt(lean_object* v_n_3_, lean_object* v_r_4_, lean_object* v_x_5_, lean_object* v_s_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = lean_nat_to_int(v_n_3_);
v___x_8_ = lean_obj_once(&lp_RequestProject_StickPolyhex_cellAt___closed__0, &lp_RequestProject_StickPolyhex_cellAt___closed__0_once, _init_lp_RequestProject_StickPolyhex_cellAt___closed__0);
v___x_9_ = lean_int_add(v___x_7_, v___x_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_int_mul(v___x_9_, v_r_4_);
lean_dec(v___x_9_);
v___x_11_ = lean_int_add(v___x_10_, v_s_6_);
lean_dec(v___x_10_);
v___x_12_ = lp_RequestProject_StickPolyhex_shearCell(v_x_5_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_cellAt___boxed(lean_object* v_n_13_, lean_object* v_r_14_, lean_object* v_x_15_, lean_object* v_s_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_RequestProject_StickPolyhex_cellAt(v_n_13_, v_r_14_, v_x_15_, v_s_16_);
lean_dec(v_s_16_);
lean_dec(v_x_15_);
lean_dec(v_r_14_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_SchematicTiling(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_EdgeRules(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_SchematicLabels(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_SchematicTiling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_EdgeRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
