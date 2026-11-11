// Lean compiler output
// Module: Tiling.Proofs.MatchingRules
// Imports: public import Init public meta import Init public import Tiling.Proofs.StickTiling
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
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
extern lean_object* lp_Tiling_StickPolyhex_HexDir_W;
lean_object* lp_Tiling_StickPolyhex_frameLabel(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_label___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_label___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_label___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_label___closed__1;
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_label___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_label___closed__2;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_label(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_label___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_label___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(6u);
v___x_2_ = lp_mathlib_ZMod_commRing(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_label___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_label___closed__0, &lp_Tiling_StickPolyhex_StickTiling_label___closed__0_once, _init_lp_Tiling_StickPolyhex_StickTiling_label___closed__0);
v___x_4_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_label___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_label___closed__1, &lp_Tiling_StickPolyhex_StickTiling_label___closed__1_once, _init_lp_Tiling_StickPolyhex_StickTiling_label___closed__1);
v___x_6_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_label(lean_object* v_n_7_, lean_object* v_T_8_, lean_object* v_c_9_, lean_object* v_e_10_){
_start:
{
lean_object* v_dir_11_; lean_object* v_idx_12_; lean_object* v___x_13_; lean_object* v_toSemiring_14_; lean_object* v___x_15_; lean_object* v_toAdd_16_; lean_object* v___x_17_; lean_object* v_toSub_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_dir_11_ = lean_ctor_get(v_T_8_, 0);
lean_inc_ref(v_dir_11_);
v_idx_12_ = lean_ctor_get(v_T_8_, 1);
lean_inc_ref(v_idx_12_);
lean_dec_ref(v_T_8_);
v___x_13_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_label___closed__0, &lp_Tiling_StickPolyhex_StickTiling_label___closed__0_once, _init_lp_Tiling_StickPolyhex_StickTiling_label___closed__0);
v_toSemiring_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref(v_toSemiring_14_);
v___x_15_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_14_);
v_toAdd_16_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_toAdd_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_label___closed__2, &lp_Tiling_StickPolyhex_StickTiling_label___closed__2_once, _init_lp_Tiling_StickPolyhex_StickTiling_label___closed__2);
v_toSub_18_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_c_9_);
v___x_19_ = lean_apply_1(v_idx_12_, v_c_9_);
v___x_20_ = lean_apply_1(v_dir_11_, v_c_9_);
lean_inc(v_toSub_18_);
v___x_21_ = lean_apply_2(v_toSub_18_, v_e_10_, v___x_20_);
v___x_22_ = lp_Tiling_StickPolyhex_HexDir_W;
v___x_23_ = lean_apply_2(v_toAdd_16_, v___x_21_, v___x_22_);
v___x_24_ = lp_Tiling_StickPolyhex_frameLabel(v_n_7_, v___x_19_, v___x_23_);
lean_dec(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_label___boxed(lean_object* v_n_25_, lean_object* v_T_26_, lean_object* v_c_27_, lean_object* v_e_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_Tiling_StickPolyhex_StickTiling_label(v_n_25_, v_T_26_, v_c_27_, v_e_28_);
lean_dec(v_n_25_);
return v_res_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_StickTiling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_MatchingRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_StickTiling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
