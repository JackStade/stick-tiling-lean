// Lean compiler output
// Module: RequestProject.ABCycle
// Imports: public import Init public meta import Init public import RequestProject.ABPhases
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
lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_sN(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_cyc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_cyc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_pha(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_pha___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_cyc(lean_object* v_D_1_, lean_object* v_m_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lp_RequestProject_StickPolyhex_ABSim_ABData_sN(v_D_1_);
v___x_4_ = lean_nat_to_int(v___x_3_);
v___x_5_ = lean_int_ediv(v_m_2_, v___x_4_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_cyc___boxed(lean_object* v_D_6_, lean_object* v_m_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_RequestProject_StickPolyhex_ABSim_ABData_cyc(v_D_6_, v_m_7_);
lean_dec(v_m_7_);
lean_dec_ref(v_D_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_pha(lean_object* v_D_9_, lean_object* v_m_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_11_ = lp_RequestProject_StickPolyhex_ABSim_ABData_sN(v_D_9_);
v___x_12_ = lean_nat_to_int(v___x_11_);
v___x_13_ = lean_int_emod(v_m_10_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = l_Int_toNat(v___x_13_);
lean_dec(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_pha___boxed(lean_object* v_D_15_, lean_object* v_m_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_RequestProject_StickPolyhex_ABSim_ABData_pha(v_D_15_, v_m_16_);
lean_dec(v_m_16_);
lean_dec_ref(v_D_15_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ABPhases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ABCycle(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ABPhases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
