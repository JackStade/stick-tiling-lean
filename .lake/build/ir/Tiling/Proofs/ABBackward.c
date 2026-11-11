// Lean compiler output
// Module: Tiling.Proofs.ABBackward
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABGadgets public import Tiling.Proofs.ABCycle public import Tiling.Proofs.ABIndex
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_sN(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_P(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_d(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_idx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_idx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg(lean_object* v_A_3_, lean_object* v_r_u2080_4_, lean_object* v_c_5_, lean_object* v_m_6_){
_start:
{
lean_object* v_V_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_V_7_ = lean_ctor_get(v_A_3_, 1);
lean_inc_ref(v_V_7_);
lean_dec_ref(v_A_3_);
v___x_8_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0, &lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0);
v___x_9_ = lean_int_mul(v___x_8_, v_c_5_);
v___x_10_ = lean_int_add(v_r_u2080_4_, v___x_9_);
lean_dec(v___x_9_);
v___x_11_ = lean_int_sub(v_r_u2080_4_, v_m_6_);
v___x_12_ = lean_apply_2(v_V_7_, v___x_10_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___boxed(lean_object* v_A_13_, lean_object* v_r_u2080_14_, lean_object* v_c_15_, lean_object* v_m_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg(v_A_13_, v_r_u2080_14_, v_c_15_, v_m_16_);
lean_dec(v_m_16_);
lean_dec(v_c_15_);
lean_dec(v_r_u2080_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv(lean_object* v_D_18_, lean_object* v_A_19_, lean_object* v_r_u2080_20_, lean_object* v_c_21_, lean_object* v_m_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg(v_A_19_, v_r_u2080_20_, v_c_21_, v_m_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Xv___boxed(lean_object* v_D_24_, lean_object* v_A_25_, lean_object* v_r_u2080_26_, lean_object* v_c_27_, lean_object* v_m_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_Tiling_StickPolyhex_ABSim_Backward_Xv(v_D_24_, v_A_25_, v_r_u2080_26_, v_c_27_, v_m_28_);
lean_dec(v_m_28_);
lean_dec(v_c_27_);
lean_dec(v_r_u2080_26_);
lean_dec_ref(v_D_24_);
return v_res_29_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___closed__0(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(1u);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg(lean_object* v_A_32_, lean_object* v_r_u2080_33_, lean_object* v_c_34_, lean_object* v_m_35_){
_start:
{
lean_object* v_V_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_V_36_ = lean_ctor_get(v_A_32_, 1);
lean_inc_ref(v_V_36_);
lean_dec_ref(v_A_32_);
v___x_37_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0, &lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg___closed__0);
v___x_38_ = lean_int_mul(v___x_37_, v_c_34_);
v___x_39_ = lean_int_add(v_r_u2080_33_, v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___closed__0, &lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___closed__0);
v___x_41_ = lean_int_add(v___x_39_, v___x_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_int_sub(v_r_u2080_33_, v_m_35_);
v___x_43_ = lean_apply_2(v_V_36_, v___x_41_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg___boxed(lean_object* v_A_44_, lean_object* v_r_u2080_45_, lean_object* v_c_46_, lean_object* v_m_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg(v_A_44_, v_r_u2080_45_, v_c_46_, v_m_47_);
lean_dec(v_m_47_);
lean_dec(v_c_46_);
lean_dec(v_r_u2080_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv(lean_object* v_D_49_, lean_object* v_A_50_, lean_object* v_r_u2080_51_, lean_object* v_c_52_, lean_object* v_m_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_Tiling_StickPolyhex_ABSim_Backward_Yv___redArg(v_A_50_, v_r_u2080_51_, v_c_52_, v_m_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_Yv___boxed(lean_object* v_D_55_, lean_object* v_A_56_, lean_object* v_r_u2080_57_, lean_object* v_c_58_, lean_object* v_m_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_Tiling_StickPolyhex_ABSim_Backward_Yv(v_D_55_, v_A_56_, v_r_u2080_57_, v_c_58_, v_m_59_);
lean_dec(v_m_59_);
lean_dec(v_c_58_);
lean_dec(v_r_u2080_57_);
lean_dec_ref(v_D_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_idx(lean_object* v_D_61_, lean_object* v_A_62_, lean_object* v_r_u2080_63_, lean_object* v_c_64_, lean_object* v_n_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_66_ = lp_Tiling_StickPolyhex_ABSim_ABData_sN(v_D_61_);
v___x_67_ = lean_nat_to_int(v___x_66_);
v___x_68_ = lean_int_mul(v___x_67_, v_n_65_);
lean_dec(v___x_67_);
v___x_69_ = lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg(v_A_62_, v_r_u2080_63_, v_c_64_, v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_61_);
v___x_71_ = lean_int_ediv(v___x_69_, v___x_70_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_idx___boxed(lean_object* v_D_72_, lean_object* v_A_73_, lean_object* v_r_u2080_74_, lean_object* v_c_75_, lean_object* v_n_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_Tiling_StickPolyhex_ABSim_Backward_idx(v_D_72_, v_A_73_, v_r_u2080_74_, v_c_75_, v_n_76_);
lean_dec(v_n_76_);
lean_dec(v_c_75_);
lean_dec(v_r_u2080_74_);
lean_dec_ref(v_D_72_);
return v_res_77_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(8u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__1(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(4u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jdx(lean_object* v_D_82_, lean_object* v_A_83_, lean_object* v_r_u2080_84_, lean_object* v_c_85_, lean_object* v_n_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_87_ = lp_Tiling_StickPolyhex_ABSim_ABData_sN(v_D_82_);
v___x_88_ = lean_nat_to_int(v___x_87_);
v___x_89_ = lean_int_mul(v___x_88_, v_n_86_);
lean_dec(v___x_88_);
v___x_90_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__0, &lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__0);
v___x_91_ = lean_int_add(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__1, &lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__1_once, _init_lp_Tiling_StickPolyhex_ABSim_Backward_jdx___closed__1);
v___x_93_ = lp_Tiling_StickPolyhex_ABSim_ABData_P(v_D_82_);
v___x_94_ = lean_nat_to_int(v___x_93_);
v___x_95_ = lean_int_mul(v___x_92_, v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_int_add(v___x_91_, v___x_95_);
lean_dec(v___x_95_);
lean_dec(v___x_91_);
v___x_97_ = lp_Tiling_StickPolyhex_ABSim_Backward_Xv___redArg(v_A_83_, v_r_u2080_84_, v_c_85_, v___x_96_);
lean_dec(v___x_96_);
v___x_98_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_82_);
v___x_99_ = lean_int_ediv(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v___x_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jdx___boxed(lean_object* v_D_100_, lean_object* v_A_101_, lean_object* v_r_u2080_102_, lean_object* v_c_103_, lean_object* v_n_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_Tiling_StickPolyhex_ABSim_Backward_jdx(v_D_100_, v_A_101_, v_r_u2080_102_, v_c_103_, v_n_104_);
lean_dec(v_n_104_);
lean_dec(v_c_103_);
lean_dec(v_r_u2080_102_);
lean_dec_ref(v_D_100_);
return v_res_105_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABGadgets(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABCycle(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABIndex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABBackward(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABGadgets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABCycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
