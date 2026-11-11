// Lean compiler output
// Module: Tiling.Proofs.Rotation
// Imports: public import Init public meta import Init public import Tiling.Proofs.Weave public import Tiling.Proofs.EdgeRules
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_ZMod_val(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rot1(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rot1inv(lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_rot1Aut___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_rot1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_rot1Aut___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_rot1Aut___closed__0_value;
static const lean_closure_object lp_Tiling_StickPolyhex_rot1Aut___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_rot1inv, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_rot1Aut___closed__1 = (const lean_object*)&lp_Tiling_StickPolyhex_rot1Aut___closed__1_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_rot1Aut___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_rot1Aut___closed__0_value),((lean_object*)&lp_Tiling_StickPolyhex_rot1Aut___closed__1_value)}};
static const lean_object* lp_Tiling_StickPolyhex_rot1Aut___closed__2 = (const lean_object*)&lp_Tiling_StickPolyhex_rot1Aut___closed__2_value;
LEAN_EXPORT const lean_object* lp_Tiling_StickPolyhex_rot1Aut = (const lean_object*)&lp_Tiling_StickPolyhex_rot1Aut___closed__2_value;
LEAN_EXPORT lean_object* lp_Tiling_AddEquiv_trans___at___00StickPolyhex_rotAut_spec__0(lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1;
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Nat_binaryRec___at___00nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotAut(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotAut___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_AddEquiv_symm___at___00StickPolyhex_unrot_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_unrot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_unrot___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rot1(lean_object* v_c_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_12_; 
v_fst_2_ = lean_ctor_get(v_c_1_, 0);
v_snd_3_ = lean_ctor_get(v_c_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_c_1_);
if (v_isSharedCheck_12_ == 0)
{
v___x_5_ = v_c_1_;
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_snd_3_);
lean_inc(v_fst_2_);
lean_dec(v_c_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_7_ = lean_int_neg(v_snd_3_);
v___x_8_ = lean_int_add(v_fst_2_, v_snd_3_);
lean_dec(v_snd_3_);
lean_dec(v_fst_2_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v___x_8_);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_10_ = v___x_5_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v___x_8_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rot1inv(lean_object* v_c_13_){
_start:
{
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_fst_14_ = lean_ctor_get(v_c_13_, 0);
v_snd_15_ = lean_ctor_get(v_c_13_, 1);
v_isSharedCheck_24_ = !lean_is_exclusive(v_c_13_);
if (v_isSharedCheck_24_ == 0)
{
v___x_17_ = v_c_13_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_snd_15_);
lean_inc(v_fst_14_);
lean_dec(v_c_13_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_19_ = lean_int_add(v_fst_14_, v_snd_15_);
lean_dec(v_snd_15_);
v___x_20_ = lean_int_neg(v_fst_14_);
lean_dec(v_fst_14_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_20_);
lean_ctor_set(v___x_17_, 0, v___x_19_);
v___x_22_ = v___x_17_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_AddEquiv_trans___at___00StickPolyhex_rotAut_spec__0(lean_object* v_h1_31_, lean_object* v_h2_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_mathlib_Equiv_trans___redArg(v_h1_31_, v_h2_32_);
return v___x_33_;
}
}
static lean_object* _init_lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0(void){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_34_;
}
}
static lean_object* _init_lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0, &lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0_once, _init_lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___lam__0(lean_object* v_y_36_, lean_object* v_x_37_){
_start:
{
lean_inc_ref(v_y_36_);
return v_y_36_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_y_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___lam__0(v_y_38_, v_x_39_);
lean_dec_ref(v_x_39_);
lean_dec_ref(v_y_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Nat_binaryRec___at___00nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3_spec__4(lean_object* v_zero_41_, lean_object* v_n_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v___y_46_; lean_object* v___y_47_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_nat_dec_eq(v_n_42_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_land(v___x_52_, v_n_42_);
v___x_57_ = lean_nat_dec_eq(v___x_56_, v___x_50_);
lean_dec(v___x_56_);
if (v___x_57_ == 0)
{
goto v___jp_53_;
}
else
{
if (v___x_51_ == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lean_nat_shiftr(v_n_42_, v___x_52_);
lean_dec(v_n_42_);
v___y_46_ = v___x_58_;
v___y_47_ = v___y_43_;
goto v___jp_45_;
}
else
{
goto v___jp_53_;
}
}
v___jp_53_:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_nat_shiftr(v_n_42_, v___x_52_);
lean_dec(v_n_42_);
lean_inc_ref(v___y_44_);
v___x_55_ = lp_mathlib_Equiv_trans___redArg(v___y_44_, v___y_43_);
v___y_46_ = v___x_54_;
v___y_47_ = v___x_55_;
goto v___jp_45_;
}
}
else
{
lean_object* v___x_59_; 
lean_dec(v_n_42_);
v___x_59_ = lean_apply_2(v_zero_41_, v___y_43_, v___y_44_);
return v___x_59_;
}
v___jp_45_:
{
lean_object* v___x_48_; 
lean_inc_ref(v___y_44_);
v___x_48_ = lp_mathlib_Equiv_trans___redArg(v___y_44_, v___y_44_);
v_n_42_ = v___y_46_;
v___y_43_ = v___y_47_;
v___y_44_ = v___x_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3(lean_object* v_k_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; 
v___f_64_ = ((lean_object*)(lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3___closed__0));
v___x_65_ = lp_Tiling_Nat_binaryRec___at___00nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3_spec__4(v___f_64_, v_k_61_, v_a_62_, v_a_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2(lean_object* v_k_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0, &lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0_once, _init_lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1___closed__0);
v___x_69_ = lp_Tiling_nsmulBinRec_go___at___00nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2_spec__3(v_k_66_, v___x_68_, v_a_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotAut(lean_object* v_k_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_unsigned_to_nat(6u);
v___x_72_ = lp_mathlib_ZMod_val(v___x_71_, v_k_70_);
v___x_73_ = ((lean_object*)(lp_Tiling_StickPolyhex_rot1Aut));
v___x_74_ = lp_Tiling_nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2(v___x_72_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotAut___boxed(lean_object* v_k_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_Tiling_StickPolyhex_rotAut(v_k_75_);
lean_dec(v_k_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2(lean_object* v_k_77_, lean_object* v_m_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_Tiling_nsmulBinRec___at___00nsmulBinRecAuto___at___00StickPolyhex_rotAut_spec__2_spec__2(v_k_77_, v_m_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotc(lean_object* v_k_80_, lean_object* v_c_81_){
_start:
{
lean_object* v___x_82_; lean_object* v_toFun_83_; lean_object* v___x_84_; 
v___x_82_ = lp_Tiling_StickPolyhex_rotAut(v_k_80_);
v_toFun_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_toFun_83_);
lean_dec_ref(v___x_82_);
v___x_84_ = lean_apply_1(v_toFun_83_, v_c_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_rotc___boxed(lean_object* v_k_85_, lean_object* v_c_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_Tiling_StickPolyhex_rotc(v_k_85_, v_c_86_);
lean_dec(v_k_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_AddEquiv_symm___at___00StickPolyhex_unrot_spec__0(lean_object* v_h_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_mathlib_Equiv_symm___redArg(v_h_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_unrot(lean_object* v_k_90_, lean_object* v_c_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_toFun_94_; lean_object* v___x_95_; 
v___x_92_ = lp_Tiling_StickPolyhex_rotAut(v_k_90_);
v___x_93_ = lp_mathlib_Equiv_symm___redArg(v___x_92_);
v_toFun_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_toFun_94_);
lean_dec_ref(v___x_93_);
v___x_95_ = lean_apply_1(v_toFun_94_, v_c_91_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_unrot___boxed(lean_object* v_k_96_, lean_object* v_c_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_Tiling_StickPolyhex_unrot(v_k_96_, v_c_97_);
lean_dec(v_k_96_);
return v_res_98_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(6u);
v___x_100_ = lp_mathlib_ZMod_commRing(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0(lean_object* v_T_101_, lean_object* v_k_102_, lean_object* v_c_103_){
_start:
{
lean_object* v___x_104_; lean_object* v_toSemiring_105_; lean_object* v___x_106_; lean_object* v_toAdd_107_; lean_object* v_dir_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_104_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0___closed__0, &lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0___closed__0_once, _init_lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0___closed__0);
v_toSemiring_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_toSemiring_105_);
v___x_106_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_105_);
v_toAdd_107_ = lean_ctor_get(v___x_106_, 1);
lean_inc(v_toAdd_107_);
lean_dec_ref(v___x_106_);
v_dir_108_ = lean_ctor_get(v_T_101_, 0);
lean_inc_ref(v_dir_108_);
lean_dec_ref(v_T_101_);
v___x_109_ = lp_Tiling_StickPolyhex_unrot(v_k_102_, v_c_103_);
v___x_110_ = lean_apply_1(v_dir_108_, v___x_109_);
v___x_111_ = lean_apply_2(v_toAdd_107_, v___x_110_, v_k_102_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__1(lean_object* v_T_112_, lean_object* v_k_113_, lean_object* v_c_114_){
_start:
{
lean_object* v_idx_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_idx_115_ = lean_ctor_get(v_T_112_, 1);
lean_inc_ref(v_idx_115_);
lean_dec_ref(v_T_112_);
v___x_116_ = lp_Tiling_StickPolyhex_unrot(v_k_113_, v_c_114_);
v___x_117_ = lean_apply_1(v_idx_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__1___boxed(lean_object* v_T_118_, lean_object* v_k_119_, lean_object* v_c_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__1(v_T_118_, v_k_119_, v_c_120_);
lean_dec(v_k_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___redArg(lean_object* v_T_122_, lean_object* v_k_123_){
_start:
{
lean_object* v___f_124_; lean_object* v___f_125_; lean_object* v___x_126_; 
lean_inc(v_k_123_);
lean_inc_ref(v_T_122_);
v___f_124_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__0), 3, 2);
lean_closure_set(v___f_124_, 0, v_T_122_);
lean_closure_set(v___f_124_, 1, v_k_123_);
v___f_125_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_StickTiling_rotate___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_125_, 0, v_T_122_);
lean_closure_set(v___f_125_, 1, v_k_123_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___f_124_);
lean_ctor_set(v___x_126_, 1, v___f_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate(lean_object* v_n_127_, lean_object* v_T_128_, lean_object* v_k_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lp_Tiling_StickPolyhex_StickTiling_rotate___redArg(v_T_128_, v_k_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_rotate___boxed(lean_object* v_n_131_, lean_object* v_T_132_, lean_object* v_k_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_Tiling_StickPolyhex_StickTiling_rotate(v_n_131_, v_T_132_, v_k_133_);
lean_dec(v_n_131_);
return v_res_134_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_Weave(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_EdgeRules(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_Rotation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_Weave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_EdgeRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1 = _init_lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1();
lean_mark_persistent(lp_Tiling_AddEquiv_refl___at___00StickPolyhex_rotAut_spec__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
