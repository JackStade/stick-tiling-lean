// Lean compiler output
// Module: RequestProject.Compactness
// Imports: public import Init public meta import Init public import Mathlib.Topology.Compactness.Compact public import Mathlib.Topology.Instances.Discrete public import RequestProject.EdgeRules public import RequestProject.StickInstance
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
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* lp_RequestProject_StickPolyhex_HexDir_W;
lean_object* lp_mathlib_TopologicalSpace_instCompleteLattice(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_nbr(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_dir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_dir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_dir___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_idx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_idx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_idx___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0;
static lean_once_cell_t lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__1;
static lean_once_cell_t lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__2;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_toLabelling___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_toLabelling(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_toLabelling___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_toStickTiling___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_toStickTiling(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_toStickTiling___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_support___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_support___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_List_elem___at___00Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_List_elem___at___00Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0(lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_Labelling_support___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_Labelling_support___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_support(lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_dir_3_; lean_object* v_idx_4_; lean_object* v_dir_5_; lean_object* v_idx_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_dir_3_ = lean_ctor_get(v_x_1_, 0);
v_idx_4_ = lean_ctor_get(v_x_1_, 1);
v_dir_5_ = lean_ctor_get(v_x_2_, 0);
v_idx_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_unsigned_to_nat(6u);
v___x_8_ = lp_mathlib_ZMod_decidableEq(v___x_7_, v_dir_3_, v_dir_5_);
if (v___x_8_ == 0)
{
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_eq(v_idx_4_, v_idx_6_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg(v_x_10_, v_x_11_);
lean_dec_ref(v_x_11_);
lean_dec_ref(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq(lean_object* v_n_14_, lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg(v_x_15_, v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___boxed(lean_object* v_n_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq(v_n_18_, v_x_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_x_19_);
lean_dec(v_n_18_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel___redArg(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg(v_x_23_, v_x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel___redArg___boxed(lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = lp_RequestProject_StickPolyhex_instDecidableEqStickLabel___redArg(v_x_26_, v_x_27_);
lean_dec_ref(v_x_27_);
lean_dec_ref(v_x_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_StickPolyhex_instDecidableEqStickLabel(lean_object* v_n_30_, lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = lp_RequestProject_StickPolyhex_instDecidableEqStickLabel_decEq___redArg(v_x_31_, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instDecidableEqStickLabel___boxed(lean_object* v_n_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = lp_RequestProject_StickPolyhex_instDecidableEqStickLabel(v_n_34_, v_x_35_, v_x_36_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_x_35_);
lean_dec(v_n_34_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_mathlib_TopologicalSpace_instCompleteLattice(lean_box(0));
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel(lean_object* v_n_40_){
_start:
{
lean_object* v___x_41_; lean_object* v_toBoundedOrder_42_; lean_object* v_toOrderBot_43_; 
v___x_41_ = lean_obj_once(&lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___closed__0, &lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___closed__0_once, _init_lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___closed__0);
v_toBoundedOrder_42_ = lean_ctor_get(v___x_41_, 3);
v_toOrderBot_43_ = lean_ctor_get(v_toBoundedOrder_42_, 1);
lean_inc(v_toOrderBot_43_);
return v_toOrderBot_43_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel___boxed(lean_object* v_n_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_RequestProject_StickPolyhex_instTopologicalSpaceStickLabel(v_n_44_);
lean_dec(v_n_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_dir___redArg(lean_object* v_f_46_, lean_object* v_c_47_){
_start:
{
lean_object* v___x_48_; lean_object* v_dir_49_; 
v___x_48_ = lean_apply_1(v_f_46_, v_c_47_);
v_dir_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_dir_49_);
lean_dec_ref(v___x_48_);
return v_dir_49_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_dir(lean_object* v_n_50_, lean_object* v_f_51_, lean_object* v_c_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_RequestProject_StickPolyhex_Labelling_dir___redArg(v_f_51_, v_c_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_dir___boxed(lean_object* v_n_54_, lean_object* v_f_55_, lean_object* v_c_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_RequestProject_StickPolyhex_Labelling_dir(v_n_54_, v_f_55_, v_c_56_);
lean_dec(v_n_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_idx___redArg(lean_object* v_f_58_, lean_object* v_c_59_){
_start:
{
lean_object* v___x_60_; lean_object* v_idx_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_apply_1(v_f_58_, v_c_59_);
v_idx_61_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_idx_61_);
lean_dec_ref(v___x_60_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_idx_61_, v___x_62_);
lean_dec(v_idx_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_idx(lean_object* v_n_64_, lean_object* v_f_65_, lean_object* v_c_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_RequestProject_StickPolyhex_Labelling_idx___redArg(v_f_65_, v_c_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_idx___boxed(lean_object* v_n_68_, lean_object* v_f_69_, lean_object* v_c_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_RequestProject_StickPolyhex_Labelling_idx(v_n_68_, v_f_69_, v_c_70_);
lean_dec(v_n_68_);
return v_res_71_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(6u);
v___x_73_ = lp_mathlib_ZMod_commRing(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__1(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0, &lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0_once, _init_lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0);
v___x_75_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__2(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__1, &lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__1_once, _init_lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__1);
v___x_77_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg(lean_object* v_R_78_, lean_object* v_f_79_, lean_object* v_c_80_, lean_object* v_e_81_){
_start:
{
lean_object* v___x_82_; lean_object* v_toSemiring_83_; lean_object* v___x_84_; lean_object* v_toAdd_85_; lean_object* v___x_86_; lean_object* v_toSub_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_82_ = lean_obj_once(&lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0, &lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0_once, _init_lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__0);
v_toSemiring_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_toSemiring_83_);
v___x_84_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_83_);
v_toAdd_85_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_toAdd_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = lean_obj_once(&lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__2, &lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__2_once, _init_lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg___closed__2);
v_toSub_87_ = lean_ctor_get(v___x_86_, 2);
lean_inc_ref(v_c_80_);
lean_inc_ref(v_f_79_);
v___x_88_ = lp_RequestProject_StickPolyhex_Labelling_idx___redArg(v_f_79_, v_c_80_);
v___x_89_ = lp_RequestProject_StickPolyhex_Labelling_dir___redArg(v_f_79_, v_c_80_);
lean_inc(v_toSub_87_);
v___x_90_ = lean_apply_2(v_toSub_87_, v_e_81_, v___x_89_);
v___x_91_ = lp_RequestProject_StickPolyhex_HexDir_W;
v___x_92_ = lean_apply_2(v_toAdd_85_, v___x_90_, v___x_91_);
v___x_93_ = lean_apply_2(v_R_78_, v___x_88_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf(lean_object* v_n_94_, lean_object* v_R_95_, lean_object* v_f_96_, lean_object* v_c_97_, lean_object* v_e_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_RequestProject_StickPolyhex_Labelling_labelOf___redArg(v_R_95_, v_f_96_, v_c_97_, v_e_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_labelOf___boxed(lean_object* v_n_100_, lean_object* v_R_101_, lean_object* v_f_102_, lean_object* v_c_103_, lean_object* v_e_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_RequestProject_StickPolyhex_Labelling_labelOf(v_n_100_, v_R_101_, v_f_102_, v_c_103_, v_e_104_);
lean_dec(v_n_100_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_toLabelling___redArg(lean_object* v_T_106_, lean_object* v_c_107_){
_start:
{
lean_object* v_dir_108_; lean_object* v_idx_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_120_; 
v_dir_108_ = lean_ctor_get(v_T_106_, 0);
v_idx_109_ = lean_ctor_get(v_T_106_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_T_106_);
if (v_isSharedCheck_120_ == 0)
{
v___x_111_ = v_T_106_;
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_idx_109_);
lean_inc(v_dir_108_);
lean_dec(v_T_106_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
lean_inc_ref(v_c_107_);
v___x_113_ = lean_apply_1(v_dir_108_, v_c_107_);
v___x_114_ = lean_apply_1(v_idx_109_, v_c_107_);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_sub(v___x_114_, v___x_115_);
lean_dec(v___x_114_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v___x_116_);
lean_ctor_set(v___x_111_, 0, v___x_113_);
v___x_118_ = v___x_111_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_toLabelling(lean_object* v_n_121_, lean_object* v_T_122_, lean_object* v_c_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lp_RequestProject_StickPolyhex_StickTiling_toLabelling___redArg(v_T_122_, v_c_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_toLabelling___boxed(lean_object* v_n_125_, lean_object* v_T_126_, lean_object* v_c_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_RequestProject_StickPolyhex_StickTiling_toLabelling(v_n_125_, v_T_126_, v_c_127_);
lean_dec(v_n_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_toStickTiling___redArg(lean_object* v_n_129_, lean_object* v_f_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
lean_inc_ref(v_f_130_);
lean_inc(v_n_129_);
v___x_131_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_Labelling_dir___boxed), 3, 2);
lean_closure_set(v___x_131_, 0, v_n_129_);
lean_closure_set(v___x_131_, 1, v_f_130_);
v___x_132_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_Labelling_idx___boxed), 3, 2);
lean_closure_set(v___x_132_, 0, v_n_129_);
lean_closure_set(v___x_132_, 1, v_f_130_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_toStickTiling(lean_object* v_n_134_, lean_object* v_R_135_, lean_object* v_f_136_, lean_object* v_h_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lp_RequestProject_StickPolyhex_Labelling_toStickTiling___redArg(v_n_134_, v_f_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_toStickTiling___boxed(lean_object* v_n_139_, lean_object* v_R_140_, lean_object* v_f_141_, lean_object* v_h_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = lp_RequestProject_StickPolyhex_Labelling_toStickTiling(v_n_139_, v_R_140_, v_f_141_, v_h_142_);
lean_dec_ref(v_R_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_support___lam__0(lean_object* v_c_144_, lean_object* v_e_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lp_RequestProject_StickPolyhex_nbr(v_c_144_, v_e_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_support___lam__0___boxed(lean_object* v_c_147_, lean_object* v_e_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_RequestProject_StickPolyhex_Labelling_support___lam__0(v_c_147_, v_e_148_);
lean_dec(v_e_148_);
lean_dec_ref(v_c_147_);
return v_res_149_;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_List_elem___at___00Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0_spec__0(lean_object* v_a_150_, lean_object* v_x_151_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
uint8_t v___x_152_; 
lean_dec_ref(v_a_150_);
v___x_152_ = 0;
return v___x_152_;
}
else
{
lean_object* v_head_153_; lean_object* v_tail_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_head_153_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_head_153_);
v_tail_154_ = lean_ctor_get(v_x_151_, 1);
lean_inc(v_tail_154_);
lean_dec_ref_known(v_x_151_, 2);
v___x_155_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc_ref(v_a_150_);
lean_inc_ref(v___x_155_);
v___x_156_ = l_instDecidableEqProd___redArg(v___x_155_, v___x_155_, v_a_150_, v_head_153_);
if (v___x_156_ == 0)
{
v_x_151_ = v_tail_154_;
goto _start;
}
else
{
lean_dec(v_tail_154_);
lean_dec_ref(v_a_150_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_List_elem___at___00Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0_spec__0___boxed(lean_object* v_a_158_, lean_object* v_x_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = lp_RequestProject_List_elem___at___00Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0_spec__0(v_a_158_, v_x_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0(lean_object* v_a_162_, lean_object* v_s_163_){
_start:
{
uint8_t v___x_164_; 
lean_inc(v_s_163_);
lean_inc_ref(v_a_162_);
v___x_164_ = lp_RequestProject_List_elem___at___00Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0_spec__0(v_a_162_, v_s_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v_a_162_);
lean_ctor_set(v___x_165_, 1, v_s_163_);
return v___x_165_;
}
else
{
lean_dec_ref(v_a_162_);
return v_s_163_;
}
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_Labelling_support___closed__0(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(6u);
v___x_167_ = lp_mathlib_ZMod_fintype___redArg(v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Labelling_support(lean_object* v_c_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc_ref(v_c_168_);
v___f_169_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_Labelling_support___lam__0___boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v_c_168_);
v___x_170_ = lean_obj_once(&lp_RequestProject_StickPolyhex_Labelling_support___closed__0, &lp_RequestProject_StickPolyhex_Labelling_support___closed__0_once, _init_lp_RequestProject_StickPolyhex_Labelling_support___closed__0);
v___x_171_ = lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(v___f_169_, v___x_170_);
v___x_172_ = lp_RequestProject_Multiset_ndinsert___at___00StickPolyhex_Labelling_support_spec__0(v_c_168_, v___x_171_);
return v___x_172_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Compactness_Compact(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Instances_Discrete(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_EdgeRules(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_StickInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_Compactness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Compactness_Compact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Instances_Discrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_EdgeRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_StickInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
