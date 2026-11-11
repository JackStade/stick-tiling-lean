// Lean compiler output
// Module: RequestProject.SchematicTiling
// Imports: public import Init public meta import Init public import RequestProject.Schematic
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
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
extern lean_object* lp_RequestProject_StickPolyhex_HexDir_W;
extern lean_object* lp_RequestProject_StickPolyhex_HexDir_SE;
extern lean_object* lp_RequestProject_StickPolyhex_HexDir_NW;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCol(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCol___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearRow(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearRow___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCell(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCell___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_bandRow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_bandRow___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_bandRow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_bandRow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_subRow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_subRow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_slotAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_slotAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_dirAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_dirAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_idxAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_idxAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_toTiling(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCol(lean_object* v_c_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; lean_object* v___x_4_; 
v_fst_2_ = lean_ctor_get(v_c_1_, 0);
v_snd_3_ = lean_ctor_get(v_c_1_, 1);
v___x_4_ = lean_int_add(v_fst_2_, v_snd_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCol___boxed(lean_object* v_c_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_RequestProject_StickPolyhex_shearCol(v_c_5_);
lean_dec_ref(v_c_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearRow(lean_object* v_c_7_){
_start:
{
lean_object* v_snd_8_; 
v_snd_8_ = lean_ctor_get(v_c_7_, 1);
lean_inc(v_snd_8_);
return v_snd_8_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearRow___boxed(lean_object* v_c_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_RequestProject_StickPolyhex_shearRow(v_c_9_);
lean_dec_ref(v_c_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCell(lean_object* v_x_11_, lean_object* v_q_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_int_sub(v_x_11_, v_q_12_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_q_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_shearCell___boxed(lean_object* v_x_15_, lean_object* v_q_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_RequestProject_StickPolyhex_shearCell(v_x_15_, v_q_16_);
lean_dec(v_x_15_);
return v_res_17_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_bandRow___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_to_int(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_bandRow(lean_object* v_n_20_, lean_object* v_q_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_22_ = lean_nat_to_int(v_n_20_);
v___x_23_ = lean_obj_once(&lp_RequestProject_StickPolyhex_bandRow___closed__0, &lp_RequestProject_StickPolyhex_bandRow___closed__0_once, _init_lp_RequestProject_StickPolyhex_bandRow___closed__0);
v___x_24_ = lean_int_add(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_int_ediv(v_q_21_, v___x_24_);
lean_dec(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_bandRow___boxed(lean_object* v_n_26_, lean_object* v_q_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_RequestProject_StickPolyhex_bandRow(v_n_26_, v_q_27_);
lean_dec(v_q_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_subRow(lean_object* v_n_29_, lean_object* v_q_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_31_ = lean_nat_to_int(v_n_29_);
v___x_32_ = lean_obj_once(&lp_RequestProject_StickPolyhex_bandRow___closed__0, &lp_RequestProject_StickPolyhex_bandRow___closed__0_once, _init_lp_RequestProject_StickPolyhex_bandRow___closed__0);
v___x_33_ = lean_int_add(v___x_31_, v___x_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_int_emod(v_q_30_, v___x_33_);
lean_dec(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_subRow___boxed(lean_object* v_n_35_, lean_object* v_q_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_RequestProject_StickPolyhex_subRow(v_n_35_, v_q_36_);
lean_dec(v_q_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf___redArg(lean_object* v_n_38_, lean_object* v_c_39_){
_start:
{
lean_object* v_snd_40_; lean_object* v___x_41_; 
v_snd_40_ = lean_ctor_get(v_c_39_, 1);
v___x_41_ = lp_RequestProject_StickPolyhex_bandRow(v_n_38_, v_snd_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf___redArg___boxed(lean_object* v_n_42_, lean_object* v_c_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_RequestProject_StickPolyhex_Schematic_bandOf___redArg(v_n_42_, v_c_43_);
lean_dec_ref(v_c_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf(lean_object* v_n_45_, lean_object* v___S_46_, lean_object* v_c_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_RequestProject_StickPolyhex_Schematic_bandOf___redArg(v_n_45_, v_c_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_bandOf___boxed(lean_object* v_n_49_, lean_object* v___S_50_, lean_object* v_c_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_RequestProject_StickPolyhex_Schematic_bandOf(v_n_49_, v___S_50_, v_c_51_);
lean_dec_ref(v_c_51_);
lean_dec_ref(v___S_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf___redArg(lean_object* v_n_53_, lean_object* v_c_54_){
_start:
{
lean_object* v_snd_55_; lean_object* v___x_56_; 
v_snd_55_ = lean_ctor_get(v_c_54_, 1);
v___x_56_ = lp_RequestProject_StickPolyhex_subRow(v_n_53_, v_snd_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf___redArg___boxed(lean_object* v_n_57_, lean_object* v_c_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_RequestProject_StickPolyhex_Schematic_subOf___redArg(v_n_57_, v_c_58_);
lean_dec_ref(v_c_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf(lean_object* v_n_60_, lean_object* v___S_61_, lean_object* v_c_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_RequestProject_StickPolyhex_Schematic_subOf___redArg(v_n_60_, v_c_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_subOf___boxed(lean_object* v_n_64_, lean_object* v___S_65_, lean_object* v_c_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_RequestProject_StickPolyhex_Schematic_subOf(v_n_64_, v___S_65_, v_c_66_);
lean_dec_ref(v_c_66_);
lean_dec_ref(v___S_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_slotAt(lean_object* v_n_68_, lean_object* v_S_69_, lean_object* v_c_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lp_RequestProject_StickPolyhex_Schematic_bandOf___redArg(v_n_68_, v_c_70_);
v___x_72_ = lp_RequestProject_StickPolyhex_shearCol(v_c_70_);
v___x_73_ = lean_apply_2(v_S_69_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_slotAt___boxed(lean_object* v_n_74_, lean_object* v_S_75_, lean_object* v_c_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_RequestProject_StickPolyhex_Schematic_slotAt(v_n_74_, v_S_75_, v_c_76_);
lean_dec_ref(v_c_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_dirAt(lean_object* v_n_78_, lean_object* v_S_79_, lean_object* v_c_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_RequestProject_StickPolyhex_Schematic_slotAt(v_n_78_, v_S_79_, v_c_80_);
switch(lean_obj_tag(v___x_81_))
{
case 0:
{
lean_object* v___x_82_; 
lean_dec_ref_known(v___x_81_, 1);
v___x_82_ = lp_RequestProject_StickPolyhex_HexDir_W;
return v___x_82_;
}
case 1:
{
lean_object* v___x_83_; 
v___x_83_ = lp_RequestProject_StickPolyhex_HexDir_SE;
return v___x_83_;
}
default: 
{
lean_object* v___x_84_; 
v___x_84_ = lp_RequestProject_StickPolyhex_HexDir_NW;
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_dirAt___boxed(lean_object* v_n_85_, lean_object* v_S_86_, lean_object* v_c_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_RequestProject_StickPolyhex_Schematic_dirAt(v_n_85_, v_S_86_, v_c_87_);
lean_dec_ref(v_c_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_idxAt(lean_object* v_n_89_, lean_object* v_S_90_, lean_object* v_c_91_){
_start:
{
lean_object* v___x_92_; 
lean_inc(v_n_89_);
v___x_92_ = lp_RequestProject_StickPolyhex_Schematic_slotAt(v_n_89_, v_S_90_, v_c_91_);
switch(lean_obj_tag(v___x_92_))
{
case 0:
{
lean_object* v_j_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_j_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_j_93_);
lean_dec_ref_known(v___x_92_, 1);
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_n_89_, v___x_94_);
lean_dec(v_n_89_);
v___x_96_ = lean_nat_sub(v___x_95_, v_j_93_);
lean_dec(v_j_93_);
lean_dec(v___x_95_);
return v___x_96_;
}
case 1:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc(v_n_89_);
v___x_97_ = lean_nat_to_int(v_n_89_);
v___x_98_ = lp_RequestProject_StickPolyhex_Schematic_subOf___redArg(v_n_89_, v_c_91_);
v___x_99_ = lean_int_sub(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v___x_97_);
v___x_100_ = l_Int_toNat(v___x_99_);
lean_dec(v___x_99_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
return v___x_102_;
}
default: 
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = lp_RequestProject_StickPolyhex_Schematic_subOf___redArg(v_n_89_, v_c_91_);
v___x_104_ = l_Int_toNat(v___x_103_);
lean_dec(v___x_103_);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v___x_104_, v___x_105_);
lean_dec(v___x_104_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_idxAt___boxed(lean_object* v_n_107_, lean_object* v_S_108_, lean_object* v_c_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_RequestProject_StickPolyhex_Schematic_idxAt(v_n_107_, v_S_108_, v_c_109_);
lean_dec_ref(v_c_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_toTiling(lean_object* v_n_111_, lean_object* v_S_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
lean_inc_ref(v_S_112_);
lean_inc(v_n_111_);
v___x_113_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_Schematic_dirAt___boxed), 3, 2);
lean_closure_set(v___x_113_, 0, v_n_111_);
lean_closure_set(v___x_113_, 1, v_S_112_);
v___x_114_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_Schematic_idxAt___boxed), 3, 2);
lean_closure_set(v___x_114_, 0, v_n_111_);
lean_closure_set(v___x_114_, 1, v_S_112_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
return v___x_115_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_Schematic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_SchematicTiling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_Schematic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
