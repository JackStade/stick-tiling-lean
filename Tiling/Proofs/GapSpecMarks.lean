import Mathlib.Tactic.Lift
import Tiling.Proofs.GapSpecData

/-!
# The computed marks are the marks of the specification

`GapSpecData.markData` computes six lists of positions from the finite bucket data.  This file
proves that the marking they describe is exactly the marking `GapSpec.marking` placed on a block
by the construction of Section 2.5 for the described specification
(`GapSpecData.toMarking_markData`), so that the marked stick prototile described by the finite
data is the prototile of the paper.
-/

namespace StickPolyhex

/-- Membership in a list built by keeping one value for each index of a range. -/
lemma mem_flatMap_ite {n : ℕ} {P : ℕ → Prop} [DecidablePred P] {f : ℕ → ℕ} {p : ℕ} :
    p ∈ (List.range n).flatMap (fun k => if P k then [f k] else []) ↔
      ∃ k < n, P k ∧ p = f k := by
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hmem⟩
    by_cases h : P k
    · rw [if_pos h] at hmem
      simp only [List.mem_singleton] at hmem
      exact ⟨k, hk, h, hmem⟩
    · rw [if_neg h] at hmem
      simp at hmem
  · rintro ⟨k, hk, h, rfl⟩
    exact ⟨k, hk, by rw [if_pos h]; simp⟩

/-- Membership in a list built by mapping a list attached to each index of a range. -/
lemma mem_flatMap_ite_map {n : ℕ} {P : ℕ → Prop} [DecidablePred P] {g : ℕ → List ℕ}
    {f : ℕ → ℕ → ℕ} {p : ℕ} :
    p ∈ (List.range n).flatMap (fun k => if P k then (g k).map (f k) else []) ↔
      ∃ k < n, P k ∧ ∃ b ∈ g k, p = f k b := by
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hmem⟩
    by_cases h : P k
    · rw [if_pos h] at hmem
      simp only [List.mem_map] at hmem
      obtain ⟨b, hb, rfl⟩ := hmem
      exact ⟨k, hk, h, b, hb, rfl⟩
    · rw [if_neg h] at hmem
      simp at hmem
  · rintro ⟨k, hk, h, b, hb, rfl⟩
    refine ⟨k, hk, ?_⟩
    rw [if_pos h]
    exact List.mem_map_of_mem hb

namespace GapSpecData

variable (G : GapSpecData)

lemma v_le_s_mul_lb : G.v ≤ G.s * G.lb := by
  have h1 := G.one_le_s
  have h2 := G.two_v_le_lb
  have : G.lb ≤ G.s * G.lb := Nat.le_mul_of_pos_left _ (by omega)
  omega

lemma v_le_k_mul_lb {k : ℕ} (hk : 1 ≤ k) : G.v ≤ k * G.lb := by
  have h2 := G.two_v_le_lb
  have : G.lb ≤ k * G.lb := Nat.le_mul_of_pos_left _ (by omega)
  omega

lemma topArrowLList_spec :
    {p : ℕ | p ∈ G.topArrowLList} = G.toGapSpec.marking.topArrowL := by
  have hv := G.one_le_v
  have hs := G.one_le_s
  have h2v : ((2 * G.v - 1 : ℕ) : ℤ) = 2 * (G.v : ℤ) - 1 := by omega
  ext p
  simp only [Set.mem_setOf_eq, topArrowLList, List.mem_append, mem_flatMap_ite,
    GapSpec.mem_topArrowL, toGapSpec_s, toGapSpec_v, toGapSpec_Imin, lbZ_eq_lb]
  constructor
  · rintro ((⟨k, hk, h1, rfl⟩ | ⟨k, hk, h1, rfl⟩) | ⟨a, ha, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl ⟨k, h1, hk, by push_cast; ring⟩
    · refine Or.inr (Or.inl ⟨k, h1, by omega, ?_⟩)
      have hilo := G.ilo_bounds k
      have e1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have e3 : ((2 * G.v + 1 - G.ilo k : ℕ) : ℤ) = 2 * (G.v : ℤ) + 1 - (G.ilo k : ℤ) := by omega
      push_cast [e1, e3, h2v]
      ring
    · refine Or.inr (Or.inr ⟨(a : ℤ), by exact_mod_cast h1, by omega, by omega, ?_⟩)
      have : ((G.v + 1 - a : ℕ) : ℤ) = (G.v : ℤ) + 1 - (a : ℤ) := by omega
      push_cast [this]
      ring
  · rintro (⟨k, h1, h2, hp⟩ | ⟨k, h1, h2, hp⟩ | ⟨a, ha1, ha2, ha3, hp⟩)
    · refine Or.inl (Or.inl ⟨k, h2, h1, ?_⟩)
      have : (p : ℤ) = ((k * G.lb : ℕ) : ℤ) := by push_cast; linarith [hp]
      exact_mod_cast this
    · refine Or.inl (Or.inr ⟨k, by omega, h1, ?_⟩)
      have hilo := G.ilo_bounds k
      have e1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have e3 : ((2 * G.v + 1 - G.ilo k : ℕ) : ℤ) = 2 * (G.v : ℤ) + 1 - (G.ilo k : ℤ) := by omega
      have : (p : ℤ) =
          (((k - 1) * G.lb + (2 * G.v - 1) * (k - 1) + (2 * G.v + 1 - G.ilo k) : ℕ) : ℤ) := by
        push_cast [e1, e3, h2v]
        linarith [hp]
      exact_mod_cast this
    · have ha0 : 0 ≤ a := by omega
      lift a to ℕ using ha0 with aN
      refine Or.inr ⟨aN, by omega, ⟨by exact_mod_cast ha1, by omega⟩, ?_⟩
      have hvle : (aN : ℤ) ≤ (G.v : ℤ) := ha2
      have : (p : ℤ) = ((G.v + 1 - aN : ℕ) : ℤ) := by
        have : ((G.v + 1 - aN : ℕ) : ℤ) = (G.v : ℤ) + 1 - (aN : ℤ) := by omega
        rw [this]
        linarith [hp]
      exact_mod_cast this

lemma topArrowRList_spec :
    {p : ℕ | p ∈ G.topArrowRList} = G.toGapSpec.marking.topArrowR := by
  have hv := G.one_le_v
  have hs := G.one_le_s
  have hvs := G.v_le_s_mul_lb
  have h2v : ((2 * G.v - 1 : ℕ) : ℤ) = 2 * (G.v : ℤ) - 1 := by omega
  ext p
  simp only [Set.mem_setOf_eq, topArrowRList, List.mem_append, mem_flatMap_ite,
    GapSpec.mem_topArrowR, toGapSpec_s, toGapSpec_v, toGapSpec_Imax, lbZ_eq_lb]
  constructor
  · rintro ((⟨k, hk, h1, rfl⟩ | ⟨k, hk, h1, rfl⟩) | ⟨b, hb, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl ⟨k, h1, hk, by push_cast; ring⟩
    · refine Or.inr (Or.inl ⟨k, h1, by omega, ?_⟩)
      have hihi := G.ihi_bounds k
      have hilo := G.ilo_bounds k
      have e1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have e3 : ((2 * G.v - 1 - G.ihi k : ℕ) : ℤ) = 2 * (G.v : ℤ) - 1 - (G.ihi k : ℤ) := by omega
      push_cast [e1, e3, h2v]
      ring
    · have hihi := G.ihi_bounds G.s
      refine Or.inr (Or.inr ⟨(b : ℤ), by exact_mod_cast h1, by omega, by omega, ?_⟩)
      have : ((G.s * G.lb - G.v + b - 1 : ℕ) : ℤ) = (G.s : ℤ) * G.lb - G.v + b - 1 := by
        have h : (G.v : ℤ) ≤ ((G.s * G.lb : ℕ) : ℤ) := by exact_mod_cast hvs
        push_cast at h ⊢
        omega
      push_cast [this]
      ring
  · rintro (⟨k, h1, h2, hp⟩ | ⟨k, h1, h2, hp⟩ | ⟨b, hb1, hb2, hb3, hp⟩)
    · refine Or.inl (Or.inl ⟨k, h2, h1, ?_⟩)
      have : (p : ℤ) = ((k * G.lb : ℕ) : ℤ) := by push_cast; linarith [hp]
      exact_mod_cast this
    · refine Or.inl (Or.inr ⟨k, by omega, h1, ?_⟩)
      have hihi := G.ihi_bounds k
      have hilo := G.ilo_bounds k
      have e1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have e3 : ((2 * G.v - 1 - G.ihi k : ℕ) : ℤ) = 2 * (G.v : ℤ) - 1 - (G.ihi k : ℤ) := by omega
      have : (p : ℤ) =
          (((k - 1) * G.lb + (2 * G.v - 1) * (k - 1) + (2 * G.v - 1 - G.ihi k) : ℕ) : ℤ) := by
        push_cast [e1, e3, h2v]
        linarith [hp]
      exact_mod_cast this
    · have hb0 : 0 ≤ b := by omega
      lift b to ℕ using hb0 with bN
      have hihi := G.ihi_bounds G.s
      refine Or.inr ⟨bN, by omega, ⟨by exact_mod_cast hb1, by omega⟩, ?_⟩
      have hcast : ((G.s * G.lb - G.v + bN - 1 : ℕ) : ℤ) = (G.s : ℤ) * G.lb - G.v + bN - 1 := by
        have h : (G.v : ℤ) ≤ ((G.s * G.lb : ℕ) : ℤ) := by exact_mod_cast hvs
        have hb : 1 ≤ (bN : ℤ) := hb1
        push_cast at h hb ⊢
        omega
      have : (p : ℤ) = ((G.s * G.lb - G.v + bN - 1 : ℕ) : ℤ) := by
        rw [hcast]
        linarith [hp]
      exact_mod_cast this

lemma botArrowLList_spec :
    {p : ℕ | p ∈ G.botArrowLList} = G.toGapSpec.marking.botArrowL := by
  have hv := G.one_le_v
  have hs := G.one_le_s
  have h2v : ((2 * G.v - 1 : ℕ) : ℤ) = 2 * (G.v : ℤ) - 1 := by omega
  have hsig : ∀ i : ℕ, 1 ≤ G.sigma i := by
    intro i; simp only [sigma]; split <;> omega
  ext p
  simp only [Set.mem_setOf_eq, botArrowLList, mem_flatMap_ite, GapSpec.mem_botArrowL,
    toGapSpec_s, toGapSpec_v, toGapSpec_sigma, lbZ_eq_lb]
  constructor
  · rintro ⟨i, hi, h1, rfl⟩
    refine ⟨i, h1, by omega, ?_⟩
    have hsi := hsig i
    have e1 : ((G.s - i : ℕ) : ℤ) = (G.s : ℤ) - i := by omega
    have e2 : ((G.sigma i - 1 : ℕ) : ℤ) = (G.sigma i : ℤ) - 1 := by omega
    push_cast [e1, e2, h2v]
    ring
  · rintro ⟨i, h1, h2, hp⟩
    refine ⟨i, by omega, h1, ?_⟩
    have hsi := hsig i
    have e1 : ((G.s - i : ℕ) : ℤ) = (G.s : ℤ) - i := by omega
    have e2 : ((G.sigma i - 1 : ℕ) : ℤ) = (G.sigma i : ℤ) - 1 := by omega
    have : (p : ℤ) =
        (((G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v + 1 : ℕ) : ℤ) := by
      push_cast [e1, e2, h2v]
      linarith [hp]
    exact_mod_cast this

lemma botArrowRList_spec :
    {p : ℕ | p ∈ G.botArrowRList} = G.toGapSpec.marking.botArrowR := by
  have hv := G.one_le_v
  have hs := G.one_le_s
  have h2v : ((2 * G.v - 1 : ℕ) : ℤ) = 2 * (G.v : ℤ) - 1 := by omega
  have hsig : ∀ i : ℕ, 1 ≤ G.sigma i := by
    intro i; simp only [sigma]; split <;> omega
  ext p
  simp only [Set.mem_setOf_eq, botArrowRList, mem_flatMap_ite, GapSpec.mem_botArrowR,
    toGapSpec_s, toGapSpec_v, toGapSpec_sigma, lbZ_eq_lb]
  constructor
  · rintro ⟨i, hi, h1, rfl⟩
    refine ⟨i, h1, by omega, ?_⟩
    have hsi := hsig i
    have e1 : ((G.s - i : ℕ) : ℤ) = (G.s : ℤ) - i := by omega
    have e2 : ((G.sigma i - 1 : ℕ) : ℤ) = (G.sigma i : ℤ) - 1 := by omega
    have e3 : (((G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v - 1 : ℕ) : ℤ)
        = (((G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v : ℕ) : ℤ) - 1 := by
      omega
    rw [e3]
    push_cast [e1, e2, h2v]
    ring
  · rintro ⟨i, h1, h2, hp⟩
    refine ⟨i, by omega, h1, ?_⟩
    have hsi := hsig i
    have e1 : ((G.s - i : ℕ) : ℤ) = (G.s : ℤ) - i := by omega
    have e2 : ((G.sigma i - 1 : ℕ) : ℤ) = (G.sigma i : ℤ) - 1 := by omega
    have e3 : (((G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v - 1 : ℕ) : ℤ)
        = (((G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v : ℕ) : ℤ) - 1 := by
      omega
    have : (p : ℤ) =
        (((G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v - 1 : ℕ) : ℤ) := by
      rw [e3]
      push_cast [e1, e2, h2v]
      linarith [hp]
    exact_mod_cast this

lemma triangleLList_spec :
    {p : ℕ | p ∈ G.triangleLList} = G.toGapSpec.marking.triangleL := by
  have hv := G.one_le_v
  have hs := G.one_le_s
  ext p
  simp only [Set.mem_setOf_eq, triangleLList, mem_flatMap_ite_map, GapSpec.mem_triangleL,
    toGapSpec_s, toGapSpec_v, toGapSpec_L, lbZ_eq_lb, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, h1, b, hb, rfl⟩
    have hbb := (G.mem_Lval).1 hb
    have hvk := G.v_le_k_mul_lb h1
    refine ⟨k, h1, by omega, (b : ℤ), ⟨b, hb, rfl⟩, ?_⟩
    have : ((k * G.lb - G.v + b : ℕ) : ℤ) = (k : ℤ) * G.lb - G.v + b := by
      have h : (G.v : ℤ) ≤ ((k * G.lb : ℕ) : ℤ) := by exact_mod_cast hvk
      push_cast at h ⊢
      omega
    push_cast [this]
    ring
  · rintro ⟨k, h1, h2, x, ⟨b, hb, rfl⟩, hp⟩
    have hbb := (G.mem_Lval).1 hb
    have hvk := G.v_le_k_mul_lb h1
    refine ⟨k, by omega, h1, b, hb, ?_⟩
    have hcast : ((k * G.lb - G.v + b : ℕ) : ℤ) = (k : ℤ) * G.lb - G.v + b := by
      have h : (G.v : ℤ) ≤ ((k * G.lb : ℕ) : ℤ) := by exact_mod_cast hvk
      push_cast at h ⊢
      omega
    have : (p : ℤ) = ((k * G.lb - G.v + b : ℕ) : ℤ) := by
      rw [hcast]
      linarith [hp]
    exact_mod_cast this

lemma triangleRList_spec :
    {p : ℕ | p ∈ G.triangleRList} = G.toGapSpec.marking.triangleR := by
  have hv := G.one_le_v
  have hs := G.one_le_s
  ext p
  simp only [Set.mem_setOf_eq, triangleRList, mem_flatMap_ite_map, GapSpec.mem_triangleR,
    toGapSpec_s, toGapSpec_v, toGapSpec_R, lbZ_eq_lb, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, h1, a, ha, rfl⟩
    have haa := (G.mem_Rval).1 ha
    refine ⟨k, h1, by omega, (a : ℤ), ⟨a, ha, rfl⟩, ?_⟩
    have e1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have : (((k - 1) * G.lb + G.v - a : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) * G.lb + G.v - a := by
      omega
    rw [this, e1]
  · rintro ⟨k, h1, h2, x, ⟨a, ha, rfl⟩, hp⟩
    have haa := (G.mem_Rval).1 ha
    refine ⟨k, by omega, h1, a, ha, ?_⟩
    have e1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have hcast : (((k - 1) * G.lb + G.v - a : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) * G.lb + G.v - a := by
      omega
    have : (p : ℤ) = (((k - 1) * G.lb + G.v - a : ℕ) : ℤ) := by
      rw [hcast, e1]
      linarith [hp]
    exact_mod_cast this

/-- **The computed marks are the marks of the specification.**  The marking described by the
lists computed from the finite bucket data is exactly the marking placed on a block by the
construction of Section 2.5. -/
theorem toMarking_markData : G.markData.toMarking = G.toGapSpec.marking := by
  have h1 := G.topArrowLList_spec
  have h2 := G.topArrowRList_spec
  have h3 := G.botArrowLList_spec
  have h4 := G.botArrowRList_spec
  have h5 := G.triangleLList_spec
  have h6 := G.triangleRList_spec
  simp only [MarkData.toMarking, markData]
  rw [h1, h2, h3, h4, h5, h6]
  cases hM : G.toGapSpec.marking
  rfl

/-- The rules of the marked stick prototile computed from the finite data are the rules of the
prototile of the paper for the described specification. -/
theorem markData_rules :
    G.markData.rules = markedRules G.toGapSpec.blockLen G.toGapSpec.marking := by
  rw [MarkData.rules, ← toMarking_markData]
  rfl

end GapSpecData

end StickPolyhex
