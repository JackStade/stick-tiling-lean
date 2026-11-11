// Lean compiler output
// Module: Tiling.Proofs.EdgeRules
// Imports: public import Init public meta import Init public import Tiling.Proofs.MatchingRules
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_Tiling_StickPolyhex_HexDir_W;
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_Tiling_StickPolyhex_HexDir_E;
lean_object* lp_Tiling_StickPolyhex_frameLabel___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0___closed__0_value;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_EdgeRules_unconstrained(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_weaveRules(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0(lean_object* v_n_3_, lean_object* v_i_4_, lean_object* v_f_5_){
_start:
{
uint8_t v___x_8_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_8_ = lean_nat_dec_eq(v_i_4_, v_n_3_);
v___x_14_ = lean_unsigned_to_nat(6u);
v___x_15_ = lp_Tiling_StickPolyhex_HexDir_E;
v___x_16_ = lp_mathlib_ZMod_decidableEq(v___x_14_, v_f_5_, v___x_15_);
if (v___x_16_ == 0)
{
goto v___jp_9_;
}
else
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_dec_eq(v_i_4_, v___x_17_);
if (v___x_18_ == 0)
{
if (v___x_16_ == 0)
{
goto v___jp_9_;
}
else
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
else
{
goto v___jp_9_;
}
}
v___jp_6_:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0___closed__0));
return v___x_7_;
}
v___jp_9_:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_10_ = lean_unsigned_to_nat(6u);
v___x_11_ = lp_Tiling_StickPolyhex_HexDir_W;
v___x_12_ = lp_mathlib_ZMod_decidableEq(v___x_10_, v_f_5_, v___x_11_);
if (v___x_12_ == 0)
{
goto v___jp_6_;
}
else
{
if (v___x_8_ == 0)
{
if (v___x_12_ == 0)
{
goto v___jp_6_;
}
else
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
else
{
goto v___jp_6_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0___boxed(lean_object* v_n_20_, lean_object* v_i_21_, lean_object* v_f_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0(v_n_20_, v_i_21_, v_f_22_);
lean_dec(v_f_22_);
lean_dec(v_i_21_);
lean_dec(v_n_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_EdgeRules_unconstrained(lean_object* v_n_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_EdgeRules_unconstrained___lam__0___boxed), 3, 1);
lean_closure_set(v___f_25_, 0, v_n_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_weaveRules(lean_object* v_n_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_frameLabel___boxed), 3, 1);
lean_closure_set(v___x_27_, 0, v_n_26_);
return v___x_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_MatchingRules(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_EdgeRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_MatchingRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
