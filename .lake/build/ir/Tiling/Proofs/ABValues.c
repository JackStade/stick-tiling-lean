// Lean compiler output
// Module: Tiling.Proofs.ABValues
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABCycle
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
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_d(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_pz(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_tz(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_kz(lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_mcorr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_mcorr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_ABData_mxv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_mxv___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_mxv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_mxv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_mcorr(lean_object* v_g_3_, lean_object* v_00_u2113_4_, lean_object* v_00_u2113_x27_5_, lean_object* v_i_6_){
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
v___x_15_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0, &lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0);
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
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_mcorr___boxed(lean_object* v_g_16_, lean_object* v_00_u2113_17_, lean_object* v_00_u2113_x27_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_Tiling_StickPolyhex_ABSim_mcorr(v_g_16_, v_00_u2113_17_, v_00_u2113_x27_18_, v_i_19_);
lean_dec(v_i_19_);
return v_res_20_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_ABData_mxv___closed__0(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(6u);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_mxv(lean_object* v_D_23_, lean_object* v_g_24_, lean_object* v_00_u2113_25_, lean_object* v_i_26_){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_dec_eq(v_i_26_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(3u);
v___x_30_ = lean_nat_dec_eq(v_i_26_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec_ref(v_g_24_);
v___x_31_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_23_);
lean_dec_ref(v_D_23_);
v___x_32_ = lean_int_mul(v___x_31_, v_00_u2113_25_);
lean_dec(v_00_u2113_25_);
lean_dec(v___x_31_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_33_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_23_);
v___x_34_ = lean_int_mul(v___x_33_, v_00_u2113_25_);
lean_dec(v___x_33_);
v___x_35_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_ABData_mxv___closed__0, &lp_Tiling_StickPolyhex_ABSim_ABData_mxv___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_ABData_mxv___closed__0);
v___x_36_ = lp_Tiling_StickPolyhex_ABSim_ABData_kz(v_D_23_);
v___x_37_ = lean_int_mul(v___x_35_, v___x_36_);
lean_dec(v___x_36_);
v___x_38_ = lean_int_add(v___x_34_, v___x_37_);
lean_dec(v___x_37_);
lean_dec(v___x_34_);
v___x_39_ = lean_apply_1(v_g_24_, v_00_u2113_25_);
v___x_40_ = lean_int_sub(v___x_38_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v___x_38_);
return v___x_40_;
}
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_23_);
lean_dec_ref(v_D_23_);
v___x_42_ = lean_int_mul(v___x_41_, v_00_u2113_25_);
lean_dec(v___x_41_);
v___x_43_ = lean_apply_1(v_g_24_, v_00_u2113_25_);
v___x_44_ = lean_int_add(v___x_42_, v___x_43_);
lean_dec(v___x_43_);
lean_dec(v___x_42_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_mxv___boxed(lean_object* v_D_45_, lean_object* v_g_46_, lean_object* v_00_u2113_47_, lean_object* v_i_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_Tiling_StickPolyhex_ABSim_ABData_mxv(v_D_45_, v_g_46_, v_00_u2113_47_, v_i_48_);
lean_dec(v_i_48_);
return v_res_49_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(2u);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp1(lean_object* v_D_54_, lean_object* v_c_55_, lean_object* v_00_u2113_56_, lean_object* v_p_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_58_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_59_ = lean_int_emod(v_c_55_, v___x_58_);
v___x_60_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0, &lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0);
v___x_61_ = lean_int_dec_eq(v___x_59_, v___x_60_);
lean_dec(v___x_59_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___y_64_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_62_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_54_);
v___x_67_ = lp_Tiling_StickPolyhex_ABSim_ABData_tz(v_D_54_);
v___x_68_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1, &lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1_once, _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1);
v___x_69_ = lean_int_add(v___x_67_, v___x_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_int_sub(v_00_u2113_56_, v_p_57_);
v___x_71_ = lean_int_dec_le(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_dec(v___x_70_);
v___y_64_ = v___x_69_;
goto v___jp_63_;
}
else
{
lean_dec(v___x_69_);
v___y_64_ = v___x_70_;
goto v___jp_63_;
}
v___jp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_int_mul(v___x_62_, v___y_64_);
lean_dec(v___y_64_);
lean_dec(v___x_62_);
v___x_66_ = lean_int_add(v___x_65_, v_p_57_);
lean_dec(v___x_65_);
return v___x_66_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_54_);
lean_dec_ref(v_D_54_);
v___x_73_ = lean_int_mul(v___x_72_, v_00_u2113_56_);
lean_dec(v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp1___boxed(lean_object* v_D_74_, lean_object* v_c_75_, lean_object* v_00_u2113_76_, lean_object* v_p_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_Tiling_StickPolyhex_ABSim_ABData_comp1(v_D_74_, v_c_75_, v_00_u2113_76_, v_p_77_);
lean_dec(v_p_77_);
lean_dec(v_00_u2113_76_);
lean_dec(v_c_75_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp1(lean_object* v_D_79_, lean_object* v_c_80_, lean_object* v_L_81_, lean_object* v_p_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_83_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_84_ = lean_int_emod(v_c_80_, v___x_83_);
v___x_85_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0, &lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0);
v___x_86_ = lean_int_dec_eq(v___x_84_, v___x_85_);
lean_dec(v___x_84_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___y_89_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_87_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_79_);
lean_inc_ref(v_D_79_);
v___x_94_ = lp_Tiling_StickPolyhex_ABSim_ABData_tz(v_D_79_);
v___x_95_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1, &lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1_once, _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__1);
v___x_96_ = lean_int_add(v___x_94_, v___x_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_int_add(v___x_96_, v_p_82_);
lean_dec(v___x_96_);
v___x_98_ = lean_int_dec_le(v_L_81_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec(v_L_81_);
v___y_89_ = v___x_97_;
goto v___jp_88_;
}
else
{
lean_dec(v___x_97_);
v___y_89_ = v_L_81_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_int_mul(v___x_87_, v___y_89_);
lean_dec(v___y_89_);
lean_dec(v___x_87_);
v___x_91_ = lp_Tiling_StickPolyhex_ABSim_ABData_pz(v_D_79_);
lean_dec_ref(v_D_79_);
v___x_92_ = lean_int_sub(v___x_91_, v_p_82_);
lean_dec(v___x_91_);
v___x_93_ = lean_int_add(v___x_90_, v___x_92_);
lean_dec(v___x_92_);
lean_dec(v___x_90_);
return v___x_93_;
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_79_);
lean_dec_ref(v_D_79_);
v___x_100_ = lean_int_mul(v___x_99_, v_L_81_);
lean_dec(v_L_81_);
lean_dec(v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp1___boxed(lean_object* v_D_101_, lean_object* v_c_102_, lean_object* v_L_103_, lean_object* v_p_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_Tiling_StickPolyhex_ABSim_ABData_exp1(v_D_101_, v_c_102_, v_L_103_, v_p_104_);
lean_dec(v_p_104_);
lean_dec(v_c_102_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp2(lean_object* v_D_106_, lean_object* v_c_107_, lean_object* v_L_108_, lean_object* v_p_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_110_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_111_ = lean_int_emod(v_c_107_, v___x_110_);
v___x_112_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0, &lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0);
v___x_113_ = lean_int_dec_eq(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_106_);
lean_dec_ref(v_D_106_);
v___x_115_ = lean_int_mul(v___x_114_, v_L_108_);
lean_dec(v___x_114_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___y_118_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_116_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_106_);
v___x_121_ = lp_Tiling_StickPolyhex_ABSim_ABData_tz(v_D_106_);
v___x_122_ = lean_int_add(v_L_108_, v_p_109_);
v___x_123_ = lean_int_dec_le(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_dec(v___x_121_);
v___y_118_ = v___x_122_;
goto v___jp_117_;
}
else
{
lean_dec(v___x_122_);
v___y_118_ = v___x_121_;
goto v___jp_117_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_int_mul(v___x_116_, v___y_118_);
lean_dec(v___y_118_);
lean_dec(v___x_116_);
v___x_120_ = lean_int_sub(v___x_119_, v_p_109_);
lean_dec(v___x_119_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp2___boxed(lean_object* v_D_124_, lean_object* v_c_125_, lean_object* v_L_126_, lean_object* v_p_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_Tiling_StickPolyhex_ABSim_ABData_comp2(v_D_124_, v_c_125_, v_L_126_, v_p_127_);
lean_dec(v_p_127_);
lean_dec(v_L_126_);
lean_dec(v_c_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp2(lean_object* v_D_129_, lean_object* v_c_130_, lean_object* v_M_131_, lean_object* v_p_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0, &lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_ABData_comp1___closed__0);
v___x_134_ = lean_int_emod(v_c_130_, v___x_133_);
v___x_135_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0, &lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_mcorr___closed__0);
v___x_136_ = lean_int_dec_eq(v___x_134_, v___x_135_);
lean_dec(v___x_134_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_129_);
lean_dec_ref(v_D_129_);
v___x_138_ = lean_int_mul(v___x_137_, v_M_131_);
lean_dec(v_M_131_);
lean_dec(v___x_137_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___y_141_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_139_ = lp_Tiling_StickPolyhex_ABSim_ABData_d(v_D_129_);
lean_inc_ref(v_D_129_);
v___x_146_ = lp_Tiling_StickPolyhex_ABSim_ABData_tz(v_D_129_);
v___x_147_ = lean_int_sub(v___x_146_, v_p_132_);
lean_dec(v___x_146_);
v___x_148_ = lean_int_dec_le(v_M_131_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v___x_147_);
v___y_141_ = v_M_131_;
goto v___jp_140_;
}
else
{
lean_dec(v_M_131_);
v___y_141_ = v___x_147_;
goto v___jp_140_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_int_mul(v___x_139_, v___y_141_);
lean_dec(v___y_141_);
lean_dec(v___x_139_);
v___x_143_ = lp_Tiling_StickPolyhex_ABSim_ABData_pz(v_D_129_);
lean_dec_ref(v_D_129_);
v___x_144_ = lean_int_sub(v___x_143_, v_p_132_);
lean_dec(v___x_143_);
v___x_145_ = lean_int_sub(v___x_142_, v___x_144_);
lean_dec(v___x_144_);
lean_dec(v___x_142_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp2___boxed(lean_object* v_D_149_, lean_object* v_c_150_, lean_object* v_M_151_, lean_object* v_p_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_Tiling_StickPolyhex_ABSim_ABData_exp2(v_D_149_, v_c_150_, v_M_151_, v_p_152_);
lean_dec(v_p_152_);
lean_dec(v_c_150_);
return v_res_153_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABCycle(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABCycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
