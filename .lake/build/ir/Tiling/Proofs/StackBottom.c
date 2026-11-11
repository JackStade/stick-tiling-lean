// Lean compiler output
// Module: Tiling.Proofs.StackBottom
// Imports: public import Init public meta import Init public import Tiling.Proofs.StackTop public import Tiling.Proofs.WeaveDown
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
lean_object* lp_Tiling_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_Tiling_StickPolyhex_StickTiling_head___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_Tiling_StickPolyhex_walk(lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_nbr(lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(6u);
v___x_2_ = lp_mathlib_ZMod_commRing(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lp_Tiling_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell___redArg(lean_object* v_T_5_, lean_object* v_u_6_, lean_object* v_y_7_, lean_object* v_j_8_){
_start:
{
lean_object* v___x_9_; lean_object* v_toSemiring_10_; lean_object* v___x_11_; lean_object* v_toAdd_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_9_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__0, &lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__0_once, _init_lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__0);
v_toSemiring_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_toSemiring_10_);
v___x_11_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_10_);
v_toAdd_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_toAdd_12_);
lean_dec_ref(v___x_11_);
v___x_13_ = lp_Tiling_StickPolyhex_StickTiling_head___redArg(v_T_5_, v_y_7_);
v___x_14_ = lean_nat_to_int(v_j_8_);
v___x_15_ = lp_Tiling_StickPolyhex_walk(v___x_13_, v_u_6_, v___x_14_);
lean_dec(v___x_14_);
v___x_16_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__1, &lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__1_once, _init_lp_Tiling_StickPolyhex_StickTiling_downCell___redArg___closed__1);
v___x_17_ = lean_apply_2(v_toAdd_12_, v_u_6_, v___x_16_);
v___x_18_ = lp_Tiling_StickPolyhex_nbr(v___x_15_, v___x_17_);
lean_dec(v___x_17_);
lean_dec_ref(v___x_15_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell(lean_object* v_n_19_, lean_object* v_T_20_, lean_object* v_u_21_, lean_object* v_y_22_, lean_object* v_j_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_Tiling_StickPolyhex_StickTiling_downCell___redArg(v_T_20_, v_u_21_, v_y_22_, v_j_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_downCell___boxed(lean_object* v_n_25_, lean_object* v_T_26_, lean_object* v_u_27_, lean_object* v_y_28_, lean_object* v_j_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_Tiling_StickPolyhex_StickTiling_downCell(v_n_25_, v_T_26_, v_u_27_, v_y_28_, v_j_29_);
lean_dec(v_n_25_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_StackTop(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_WeaveDown(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_StackBottom(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_StackTop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_WeaveDown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
