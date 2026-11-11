// Lean compiler output
// Module: Tiling.Proofs.GapSpec
// Imports: public import Init public meta import Init public import Tiling.Proofs.Markings public import Tiling.Proofs.GapGeometry
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lb(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lb___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_blockLen(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_blockLen___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_sigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_sigma___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lbZ(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lbZ___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_marking(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_marking___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lb(lean_object* v_G_1_){
_start:
{
lean_object* v_s_2_; lean_object* v_v_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_s_2_ = lean_ctor_get(v_G_1_, 0);
v_v_3_ = lean_ctor_get(v_G_1_, 1);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_mul(v___x_4_, v_v_3_);
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_sub(v___x_5_, v___x_6_);
v___x_8_ = lean_nat_sub(v_s_2_, v___x_6_);
v___x_9_ = lean_nat_mul(v___x_7_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_nat_add(v___x_9_, v___x_5_);
lean_dec(v___x_5_);
lean_dec(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lb___boxed(lean_object* v_G_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_Tiling_StickPolyhex_GapSpec_lb(v_G_11_);
lean_dec_ref(v_G_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_blockLen(lean_object* v_G_13_){
_start:
{
lean_object* v_s_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_s_14_ = lean_ctor_get(v_G_13_, 0);
v___x_15_ = lp_Tiling_StickPolyhex_GapSpec_lb(v_G_13_);
v___x_16_ = lean_nat_mul(v_s_14_, v___x_15_);
lean_dec(v___x_15_);
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_nat_add(v___x_16_, v___x_17_);
lean_dec(v___x_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_blockLen___boxed(lean_object* v_G_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_Tiling_StickPolyhex_GapSpec_blockLen(v_G_19_);
lean_dec_ref(v_G_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_sigma(lean_object* v_G_21_, lean_object* v_i_22_){
_start:
{
lean_object* v_s_23_; uint8_t v___x_24_; 
v_s_23_ = lean_ctor_get(v_G_21_, 0);
v___x_24_ = lean_nat_dec_eq(v_i_22_, v_s_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v_i_22_, v___x_25_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(1u);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_sigma___boxed(lean_object* v_G_28_, lean_object* v_i_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_Tiling_StickPolyhex_GapSpec_sigma(v_G_28_, v_i_29_);
lean_dec(v_i_29_);
lean_dec_ref(v_G_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lbZ(lean_object* v_G_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lp_Tiling_StickPolyhex_GapSpec_lb(v_G_31_);
v___x_33_ = lean_nat_to_int(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_lbZ___boxed(lean_object* v_G_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_Tiling_StickPolyhex_GapSpec_lbZ(v_G_34_);
lean_dec_ref(v_G_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_marking(lean_object* v_G_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpec_marking___boxed(lean_object* v_G_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_Tiling_StickPolyhex_GapSpec_marking(v_G_38_);
lean_dec_ref(v_G_38_);
return v_res_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_Markings(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_GapGeometry(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_GapSpec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_Markings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_GapGeometry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
