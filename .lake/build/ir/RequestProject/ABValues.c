// Lean compiler output
// Module: RequestProject.ABValues
// Imports: public import Init public meta import Init public import RequestProject.ABCycle
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
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_d(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_pz(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_tz(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_mcorr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_mcorr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_mxv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_mxv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0;
static lean_once_cell_t lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_mcorr(lean_object* v_g_3_, lean_object* v_00_u2113_4_, lean_object* v_00_u2113_x27_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(2u);
v___x_12_ = lean_nat_dec_eq(v_i_6_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(3u);
v___x_14_ = lean_nat_dec_eq(v_i_6_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec(v_00_u2113_x27_5_);
lean_dec(v_00_u2113_4_);
lean_dec_ref(v_g_3_);
v___x_15_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0, &lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0);
return v___x_15_;
}
else
{
goto v___jp_7_;
}
}
else
{
goto v___jp_7_;
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
lean_inc_ref(v_g_3_);
v___x_8_ = lean_apply_1(v_g_3_, v_00_u2113_x27_5_);
v___x_9_ = lean_apply_1(v_g_3_, v_00_u2113_4_);
v___x_10_ = lean_int_sub(v___x_8_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v___x_8_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_mcorr___boxed(lean_object* v_g_16_, lean_object* v_00_u2113_17_, lean_object* v_00_u2113_x27_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_RequestProject_StickPolyhex_ABSim_mcorr(v_g_16_, v_00_u2113_17_, v_00_u2113_x27_18_, v_i_19_);
lean_dec(v_i_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_mxv(lean_object* v_D_21_, lean_object* v_g_22_, lean_object* v_00_u2113_23_, lean_object* v_i_24_){
_start:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_dec_eq(v_i_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(3u);
v___x_28_ = lean_nat_dec_eq(v_i_24_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec_ref(v_g_22_);
v___x_29_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_21_);
v___x_30_ = lean_int_mul(v___x_29_, v_00_u2113_23_);
lean_dec(v_00_u2113_23_);
lean_dec(v___x_29_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_31_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_21_);
v___x_32_ = lean_int_mul(v___x_31_, v_00_u2113_23_);
lean_dec(v___x_31_);
v___x_33_ = lean_apply_1(v_g_22_, v_00_u2113_23_);
v___x_34_ = lean_int_sub(v___x_32_, v___x_33_);
lean_dec(v___x_33_);
lean_dec(v___x_32_);
return v___x_34_;
}
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_21_);
v___x_36_ = lean_int_mul(v___x_35_, v_00_u2113_23_);
lean_dec(v___x_35_);
v___x_37_ = lean_apply_1(v_g_22_, v_00_u2113_23_);
v___x_38_ = lean_int_add(v___x_36_, v___x_37_);
lean_dec(v___x_37_);
lean_dec(v___x_36_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_mxv___boxed(lean_object* v_D_39_, lean_object* v_g_40_, lean_object* v_00_u2113_41_, lean_object* v_i_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_RequestProject_StickPolyhex_ABSim_ABData_mxv(v_D_39_, v_g_40_, v_00_u2113_41_, v_i_42_);
lean_dec(v_i_42_);
lean_dec_ref(v_D_39_);
return v_res_43_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(2u);
v___x_45_ = lean_nat_to_int(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp1(lean_object* v_D_48_, lean_object* v_c_49_, lean_object* v_00_u2113_50_, lean_object* v_p_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_52_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_53_ = lean_int_emod(v_c_49_, v___x_52_);
v___x_54_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0, &lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0);
v___x_55_ = lean_int_dec_eq(v___x_53_, v___x_54_);
lean_dec(v___x_53_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___y_58_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_56_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_48_);
v___x_61_ = lp_RequestProject_StickPolyhex_ABSim_ABData_tz(v_D_48_);
v___x_62_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1, &lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1_once, _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1);
v___x_63_ = lean_int_add(v___x_61_, v___x_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_int_sub(v_00_u2113_50_, v_p_51_);
v___x_65_ = lean_int_dec_le(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_dec(v___x_64_);
v___y_58_ = v___x_63_;
goto v___jp_57_;
}
else
{
lean_dec(v___x_63_);
v___y_58_ = v___x_64_;
goto v___jp_57_;
}
v___jp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_int_mul(v___x_56_, v___y_58_);
lean_dec(v___y_58_);
lean_dec(v___x_56_);
v___x_60_ = lean_int_add(v___x_59_, v_p_51_);
lean_dec(v___x_59_);
return v___x_60_;
}
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_48_);
lean_dec_ref(v_D_48_);
v___x_67_ = lean_int_mul(v___x_66_, v_00_u2113_50_);
lean_dec(v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___boxed(lean_object* v_D_68_, lean_object* v_c_69_, lean_object* v_00_u2113_70_, lean_object* v_p_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_RequestProject_StickPolyhex_ABSim_ABData_comp1(v_D_68_, v_c_69_, v_00_u2113_70_, v_p_71_);
lean_dec(v_p_71_);
lean_dec(v_00_u2113_70_);
lean_dec(v_c_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp1(lean_object* v_D_73_, lean_object* v_c_74_, lean_object* v_L_75_, lean_object* v_p_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_77_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_78_ = lean_int_emod(v_c_74_, v___x_77_);
v___x_79_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0, &lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0);
v___x_80_ = lean_int_dec_eq(v___x_78_, v___x_79_);
lean_dec(v___x_78_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___y_83_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_81_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_73_);
lean_inc_ref(v_D_73_);
v___x_88_ = lp_RequestProject_StickPolyhex_ABSim_ABData_tz(v_D_73_);
v___x_89_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1, &lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1_once, _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__1);
v___x_90_ = lean_int_add(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_int_add(v___x_90_, v_p_76_);
lean_dec(v___x_90_);
v___x_92_ = lean_int_dec_le(v_L_75_, v___x_91_);
if (v___x_92_ == 0)
{
lean_dec(v_L_75_);
v___y_83_ = v___x_91_;
goto v___jp_82_;
}
else
{
lean_dec(v___x_91_);
v___y_83_ = v_L_75_;
goto v___jp_82_;
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = lean_int_mul(v___x_81_, v___y_83_);
lean_dec(v___y_83_);
lean_dec(v___x_81_);
v___x_85_ = lp_RequestProject_StickPolyhex_ABSim_ABData_pz(v_D_73_);
lean_dec_ref(v_D_73_);
v___x_86_ = lean_int_sub(v___x_85_, v_p_76_);
lean_dec(v___x_85_);
v___x_87_ = lean_int_add(v___x_84_, v___x_86_);
lean_dec(v___x_86_);
lean_dec(v___x_84_);
return v___x_87_;
}
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_73_);
lean_dec_ref(v_D_73_);
v___x_94_ = lean_int_mul(v___x_93_, v_L_75_);
lean_dec(v_L_75_);
lean_dec(v___x_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp1___boxed(lean_object* v_D_95_, lean_object* v_c_96_, lean_object* v_L_97_, lean_object* v_p_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_RequestProject_StickPolyhex_ABSim_ABData_exp1(v_D_95_, v_c_96_, v_L_97_, v_p_98_);
lean_dec(v_p_98_);
lean_dec(v_c_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp2(lean_object* v_D_100_, lean_object* v_c_101_, lean_object* v_L_102_, lean_object* v_p_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_104_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_105_ = lean_int_emod(v_c_101_, v___x_104_);
v___x_106_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0, &lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0);
v___x_107_ = lean_int_dec_eq(v___x_105_, v___x_106_);
lean_dec(v___x_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_100_);
lean_dec_ref(v_D_100_);
v___x_109_ = lean_int_mul(v___x_108_, v_L_102_);
lean_dec(v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___y_112_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_110_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_100_);
v___x_115_ = lp_RequestProject_StickPolyhex_ABSim_ABData_tz(v_D_100_);
v___x_116_ = lean_int_add(v_L_102_, v_p_103_);
v___x_117_ = lean_int_dec_le(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_dec(v___x_115_);
v___y_112_ = v___x_116_;
goto v___jp_111_;
}
else
{
lean_dec(v___x_116_);
v___y_112_ = v___x_115_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_int_mul(v___x_110_, v___y_112_);
lean_dec(v___y_112_);
lean_dec(v___x_110_);
v___x_114_ = lean_int_sub(v___x_113_, v_p_103_);
lean_dec(v___x_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_comp2___boxed(lean_object* v_D_118_, lean_object* v_c_119_, lean_object* v_L_120_, lean_object* v_p_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_RequestProject_StickPolyhex_ABSim_ABData_comp2(v_D_118_, v_c_119_, v_L_120_, v_p_121_);
lean_dec(v_p_121_);
lean_dec(v_L_120_);
lean_dec(v_c_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp2(lean_object* v_D_123_, lean_object* v_c_124_, lean_object* v_M_125_, lean_object* v_p_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_127_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_128_ = lean_int_emod(v_c_124_, v___x_127_);
v___x_129_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0, &lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_mcorr___closed__0);
v___x_130_ = lean_int_dec_eq(v___x_128_, v___x_129_);
lean_dec(v___x_128_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_123_);
lean_dec_ref(v_D_123_);
v___x_132_ = lean_int_mul(v___x_131_, v_M_125_);
lean_dec(v_M_125_);
lean_dec(v___x_131_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___y_135_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_133_ = lp_RequestProject_StickPolyhex_ABSim_ABData_d(v_D_123_);
lean_inc_ref(v_D_123_);
v___x_140_ = lp_RequestProject_StickPolyhex_ABSim_ABData_tz(v_D_123_);
v___x_141_ = lean_int_sub(v___x_140_, v_p_126_);
lean_dec(v___x_140_);
v___x_142_ = lean_int_dec_le(v_M_125_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec(v___x_141_);
v___y_135_ = v_M_125_;
goto v___jp_134_;
}
else
{
lean_dec(v_M_125_);
v___y_135_ = v___x_141_;
goto v___jp_134_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_136_ = lean_int_mul(v___x_133_, v___y_135_);
lean_dec(v___y_135_);
lean_dec(v___x_133_);
v___x_137_ = lp_RequestProject_StickPolyhex_ABSim_ABData_pz(v_D_123_);
lean_dec_ref(v_D_123_);
v___x_138_ = lean_int_sub(v___x_137_, v_p_126_);
lean_dec(v___x_137_);
v___x_139_ = lean_int_sub(v___x_136_, v___x_138_);
lean_dec(v___x_138_);
lean_dec(v___x_136_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_exp2___boxed(lean_object* v_D_143_, lean_object* v_c_144_, lean_object* v_M_145_, lean_object* v_p_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = lp_RequestProject_StickPolyhex_ABSim_ABData_exp2(v_D_143_, v_c_144_, v_M_145_, v_p_146_);
lean_dec(v_p_146_);
lean_dec(v_c_144_);
return v_res_147_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ABCycle(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ABValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ABCycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
