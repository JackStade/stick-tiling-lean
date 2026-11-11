// Lean compiler output
// Module: Tiling.Proofs.ABTiling
// Imports: public import Init public meta import Init public import Tiling.Proofs.Prelude public import Tiling.MainResults.ABTiling
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* lp_lean__wang_LeanWang_WangTile_equivTuple;
lean_object* lp_mathlib_Equiv_sigmaEquivProd(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_lean__wang_Encodable_encodeSigma___at___00Encodable_encodeList___at___00LeanWang_encodeTileSet_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_wangColor(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_wangColor___boxed(lean_object*);
static lean_once_cell_t lp_Tiling_Tiling_AB_linkColor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_linkColor___closed__0;
static lean_once_cell_t lp_Tiling_Tiling_AB_linkColor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_linkColor___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_linkColor(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_toA(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_toB(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00Tiling_AB_reduceAB_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00Tiling_AB_reduceAB_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_reduceAB(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_wangColor(lean_object* v_c_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_2_ = lean_unsigned_to_nat(2u);
v___x_3_ = lean_nat_mul(v___x_2_, v_c_1_);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_wangColor___boxed(lean_object* v_c_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_Tiling_Tiling_AB_wangColor(v_c_6_);
lean_dec(v_c_6_);
return v_res_7_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_linkColor___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_mathlib_Equiv_sigmaEquivProd(lean_box(0), lean_box(0));
return v___x_8_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_linkColor___closed__1(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&lp_Tiling_Tiling_AB_linkColor___closed__0, &lp_Tiling_Tiling_AB_linkColor___closed__0_once, _init_lp_Tiling_Tiling_AB_linkColor___closed__0);
v___x_10_ = lp_mathlib_Equiv_symm___redArg(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_linkColor(lean_object* v_t_11_){
_start:
{
lean_object* v___x_12_; lean_object* v_toFun_13_; lean_object* v___x_14_; lean_object* v_toFun_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_12_ = lp_lean__wang_LeanWang_WangTile_equivTuple;
v_toFun_13_ = lean_ctor_get(v___x_12_, 0);
v___x_14_ = lean_obj_once(&lp_Tiling_Tiling_AB_linkColor___closed__1, &lp_Tiling_Tiling_AB_linkColor___closed__1_once, _init_lp_Tiling_Tiling_AB_linkColor___closed__1);
v_toFun_15_ = lean_ctor_get(v___x_14_, 0);
v___x_16_ = lean_unsigned_to_nat(2u);
lean_inc(v_toFun_13_);
v___x_17_ = lean_apply_1(v_toFun_13_, v_t_11_);
lean_inc(v_toFun_15_);
v___x_18_ = lean_apply_1(v_toFun_15_, v___x_17_);
v___x_19_ = lp_lean__wang_Encodable_encodeSigma___at___00Encodable_encodeList___at___00LeanWang_encodeTileSet_spec__0_spec__0(v___x_18_);
v___x_20_ = lean_nat_mul(v___x_16_, v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = lean_nat_add(v___x_20_, v___x_16_);
lean_dec(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_toA(lean_object* v_t_22_){
_start:
{
lean_object* v_n_23_; lean_object* v_w_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_n_23_ = lean_ctor_get(v_t_22_, 0);
v_w_24_ = lean_ctor_get(v_t_22_, 3);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lp_Tiling_Tiling_AB_wangColor(v_n_23_);
v___x_27_ = lp_Tiling_Tiling_AB_wangColor(v_w_24_);
v___x_28_ = lp_Tiling_Tiling_AB_linkColor(v_t_22_);
v___x_29_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_29_, 0, v___x_25_);
lean_ctor_set(v___x_29_, 1, v___x_26_);
lean_ctor_set(v___x_29_, 2, v___x_27_);
lean_ctor_set(v___x_29_, 3, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_toB(lean_object* v_t_30_){
_start:
{
lean_object* v_s_31_; lean_object* v_e_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_s_31_ = lean_ctor_get(v_t_30_, 1);
lean_inc(v_s_31_);
v_e_32_ = lean_ctor_get(v_t_30_, 2);
lean_inc(v_e_32_);
v___x_33_ = lp_Tiling_Tiling_AB_linkColor(v_t_30_);
v___x_34_ = lp_Tiling_Tiling_AB_wangColor(v_e_32_);
lean_dec(v_e_32_);
v___x_35_ = lp_Tiling_Tiling_AB_wangColor(v_s_31_);
lean_dec(v_s_31_);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_37_, 0, v___x_33_);
lean_ctor_set(v___x_37_, 1, v___x_34_);
lean_ctor_set(v___x_37_, 2, v___x_35_);
lean_ctor_set(v___x_37_, 3, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00Tiling_AB_reduceAB_spec__0(lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
if (lean_obj_tag(v_a_38_) == 0)
{
lean_object* v___x_40_; 
v___x_40_ = l_List_reverse___redArg(v_a_39_);
return v___x_40_;
}
else
{
lean_object* v_head_41_; lean_object* v_tail_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_51_; 
v_head_41_ = lean_ctor_get(v_a_38_, 0);
v_tail_42_ = lean_ctor_get(v_a_38_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_a_38_);
if (v_isSharedCheck_51_ == 0)
{
v___x_44_ = v_a_38_;
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_tail_42_);
lean_inc(v_head_41_);
lean_dec(v_a_38_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = lp_Tiling_Tiling_AB_toA(v_head_41_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v_a_39_);
lean_ctor_set(v___x_44_, 0, v___x_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_a_39_);
v___x_48_ = v_reuseFailAlloc_50_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
v_a_38_ = v_tail_42_;
v_a_39_ = v___x_48_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00Tiling_AB_reduceAB_spec__1(lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
if (lean_obj_tag(v_a_52_) == 0)
{
lean_object* v___x_54_; 
v___x_54_ = l_List_reverse___redArg(v_a_53_);
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_65_; 
v_head_55_ = lean_ctor_get(v_a_52_, 0);
v_tail_56_ = lean_ctor_get(v_a_52_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_a_52_);
if (v_isSharedCheck_65_ == 0)
{
v___x_58_ = v_a_52_;
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_tail_56_);
lean_inc(v_head_55_);
lean_dec(v_a_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lp_Tiling_Tiling_AB_toB(v_head_55_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v_a_53_);
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_a_53_);
v___x_62_ = v_reuseFailAlloc_64_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
v_a_52_ = v_tail_56_;
v_a_53_ = v___x_62_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_reduceAB(lean_object* v_T_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = lean_box(0);
lean_inc(v_T_66_);
v___x_68_ = lp_Tiling_List_mapTR_loop___at___00Tiling_AB_reduceAB_spec__0(v_T_66_, v___x_67_);
v___x_69_ = lp_Tiling_List_mapTR_loop___at___00Tiling_AB_reduceAB_spec__1(v_T_66_, v___x_67_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_Prelude(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_MainResults_ABTiling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABTiling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_MainResults_ABTiling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
