// Lean compiler output
// Module: Tiling.Proofs.GapConditions
// Imports: public import Init public meta import Init public import Tiling.Proofs.GapSpec public import Tiling.Proofs.MarkedTiling
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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_GapSpec_lval___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_GapSpec_lval___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_GapSpec_lval___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_GapSpec_lval___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_rval(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_GapSpec_lval___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_GapSpec_lval___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lval(lean_object* v_G_5_, lean_object* v_k_6_, lean_object* v_l_7_){
_start:
{
lean_object* v_v_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_v_8_ = lean_ctor_get(v_G_5_, 1);
lean_inc(v_v_8_);
lean_dec_ref(v_G_5_);
v___x_9_ = lean_nat_to_int(v_l_7_);
v___x_10_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapSpec_lval___closed__0, &lp_Tiling_StickPolyhex_GapSpec_lval___closed__0_once, _init_lp_Tiling_StickPolyhex_GapSpec_lval___closed__0);
v___x_11_ = lean_nat_to_int(v_v_8_);
v___x_12_ = lean_int_mul(v___x_10_, v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapSpec_lval___closed__1, &lp_Tiling_StickPolyhex_GapSpec_lval___closed__1_once, _init_lp_Tiling_StickPolyhex_GapSpec_lval___closed__1);
v___x_14_ = lean_int_sub(v___x_12_, v___x_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_nat_to_int(v_k_6_);
v___x_16_ = lean_int_sub(v___x_15_, v___x_13_);
lean_dec(v___x_15_);
v___x_17_ = lean_int_mul(v___x_14_, v___x_16_);
lean_dec(v___x_16_);
lean_dec(v___x_14_);
v___x_18_ = lean_int_sub(v___x_9_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_9_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_rval(lean_object* v_G_19_, lean_object* v_k_20_, lean_object* v_m_21_){
_start:
{
lean_object* v_s_22_; lean_object* v_v_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_s_22_ = lean_ctor_get(v_G_19_, 0);
lean_inc(v_s_22_);
v_v_23_ = lean_ctor_get(v_G_19_, 1);
lean_inc(v_v_23_);
lean_dec_ref(v_G_19_);
v___x_24_ = lean_nat_to_int(v_m_21_);
v___x_25_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapSpec_lval___closed__0, &lp_Tiling_StickPolyhex_GapSpec_lval___closed__0_once, _init_lp_Tiling_StickPolyhex_GapSpec_lval___closed__0);
v___x_26_ = lean_nat_to_int(v_v_23_);
v___x_27_ = lean_int_mul(v___x_25_, v___x_26_);
lean_dec(v___x_26_);
v___x_28_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapSpec_lval___closed__1, &lp_Tiling_StickPolyhex_GapSpec_lval___closed__1_once, _init_lp_Tiling_StickPolyhex_GapSpec_lval___closed__1);
v___x_29_ = lean_int_sub(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_nat_to_int(v_s_22_);
v___x_31_ = lean_nat_to_int(v_k_20_);
v___x_32_ = lean_int_sub(v___x_30_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_int_mul(v___x_29_, v___x_32_);
lean_dec(v___x_32_);
lean_dec(v___x_29_);
v___x_34_ = lean_int_sub(v___x_24_, v___x_33_);
lean_dec(v___x_33_);
lean_dec(v___x_24_);
return v___x_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_GapSpec(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_MarkedTiling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_GapConditions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_GapSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_MarkedTiling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
