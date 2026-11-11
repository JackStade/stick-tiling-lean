import Tiling.Proofs.ABBucketLists

/-!
# The finite specification of an AB tile set

`ABSim.abSpecData S` is the finite form (a `GapSpecData`) of the specification of Section 2.5
attached to the AB tile set `S` by Sections 2.6–2.8.  The main result of this file,
`ABSim.abSpecData_toGapSpec`, is that reading it back as a `GapSpec` gives exactly
`(ABSim.abData S hA).spec`, so that the finite data describes the specification of the paper.
-/

namespace StickPolyhex

lemma GapSpec.ext' {G H : GapSpec} (hs : G.s = H.s) (hv : G.v = H.v) (hL : G.L = H.L)
    (hR : G.R = H.R) (hmin : G.Imin = H.Imin) (hmax : G.Imax = H.Imax) : G = H := by
  cases G
  cases H
  simp only at hs hv hL hR hmin hmax
  subst hs
  subst hv
  subst hL
  subst hR
  subst hmin
  subst hmax
  rfl

lemma getD_map_range {α : Type*} (f : ℕ → α) (d : α) (n k : ℕ) :
    ((List.range n).map f).getD k d = if k < n then f k else d := by
  by_cases h : k < n
  · rw [if_pos h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [if_neg h, List.getD_eq_default]
    simp only [List.length_map, List.length_range]
    omega

namespace ABSim

open Tiling.AB

variable (S : ABTileSet)

/-- The finite form of the specification of Section 2.5 attached to a set of AB tiles. -/
def abSpecData : GapSpecData where
  sRaw := sN S
  vRaw := vN S
  Lraw := (List.range (sN S + 1)).map (fun q => (dataList S q).L)
  Rraw := (List.range (sN S + 1)).map (fun q => (dataList S q).R)
  IloRaw := (List.range (sN S + 1)).map (fun q => (dataList S q).lo)
  IhiRaw := (List.range (sN S + 1)).map (fun q => (dataList S q).hi)

lemma one_le_vN : 1 ≤ vN S := by
  have h1 := twelve_kN_le_dN S
  have h2 := one_le_kN S
  have h3 := vN_eq S
  omega

@[simp] lemma abSpecData_s : (abSpecData S).s = sN S := by
  simp only [GapSpecData.s, abSpecData, sN]
  omega

@[simp] lemma abSpecData_v : (abSpecData S).v = vN S := by
  have := one_le_vN S
  simp only [GapSpecData.v, abSpecData]
  omega

/-- Above the last bucket the table of the construction is empty. -/
lemma data_out {q : ℕ} (hq : sN S < q) (hA : S.A ≠ []) :
    ((abData S hA).data q).L = ∅ ∧ ((abData S hA).data q).R = ∅ ∧
      ((abData S hA).data q).lo = 0 ∧ ((abData S hA).data q).hi = 0 := by
  have hp : 17 + 4 * pN S < sN S := by
    have := one_le_pN S
    simp only [sN, pN] at *
    omega
  simp only [ABData.data, abData_P, abData_sN]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact ⟨rfl, rfl, rfl, rfl⟩

variable (hA : S.A ≠ [])

include hA in
lemma abSpecData_L (k : ℕ) : (abSpecData S).toGapSpec.L k = ((abData S hA).data k).L := by
  have hv := abSpecData_v S
  have hs := abSpecData_s S
  ext x
  simp only [GapSpecData.toGapSpec_L, Set.mem_setOf_eq, GapSpecData.mem_Lval]
  by_cases hk : k ≤ sN S
  · have hl := (dataList_agrees S hA k).1
    have hget : (abSpecData S).Lraw.getD k [] = (dataList S k).L := by
      simp only [abSpecData, getD_map_range]
      rw [if_pos (by omega)]
    rw [hget, hv]
    constructor
    · rintro ⟨b, ⟨hb, -, -⟩, rfl⟩
      exact (hl.2 _).2 ⟨b, hb, rfl⟩
    · intro hx
      obtain ⟨b, hb, rfl⟩ := (hl.2 x).1 hx
      exact ⟨b, ⟨hb, hl.1 b hb⟩, rfl⟩
  · have hget : (abSpecData S).Lraw.getD k [] = [] := by
      simp only [abSpecData, getD_map_range]
      rw [if_neg (by omega)]
    rw [hget, (data_out S (by omega) hA).1]
    simp

include hA in
lemma abSpecData_R (k : ℕ) : (abSpecData S).toGapSpec.R k = ((abData S hA).data k).R := by
  have hv := abSpecData_v S
  have hs := abSpecData_s S
  ext x
  simp only [GapSpecData.toGapSpec_R, Set.mem_setOf_eq, GapSpecData.mem_Rval]
  by_cases hk : k ≤ sN S
  · have hl := (dataList_agrees S hA k).2.1
    have hget : (abSpecData S).Rraw.getD k [] = (dataList S k).R := by
      simp only [abSpecData, getD_map_range]
      rw [if_pos (by omega)]
    rw [hget, hv]
    constructor
    · rintro ⟨b, ⟨hb, -, -⟩, rfl⟩
      exact (hl.2 _).2 ⟨b, hb, rfl⟩
    · intro hx
      obtain ⟨b, hb, rfl⟩ := (hl.2 x).1 hx
      exact ⟨b, ⟨hb, hl.1 b hb⟩, rfl⟩
  · have hget : (abSpecData S).Rraw.getD k [] = [] := by
      simp only [abSpecData, getD_map_range]
      rw [if_neg (by omega)]
    rw [hget, (data_out S (by omega) hA).2.1]
    simp

include hA in
lemma abSpecData_Imin (k : ℕ) :
    (abSpecData S).toGapSpec.Imin k = ((abData S hA).data k).lo := by
  have hv := abSpecData_v S
  have hvpos := one_le_vN S
  have hint := (abData S hA).data_interval k
  have hvz : (abData S hA).vz = (vN S : ℤ) := rfl
  rw [hvz] at hint
  simp only [GapSpecData.toGapSpec_Imin, GapSpecData.ilo, hv]
  by_cases hk : k ≤ sN S
  · have hlo := (dataList_agrees S hA k).2.2.1
    have hget : (abSpecData S).IloRaw.getD k (vN S) = (dataList S k).lo := by
      simp only [abSpecData, getD_map_range]
      rw [if_pos (by omega)]
    rw [hget]
    have h1 : 1 ≤ (dataList S k).lo := by
      have : ((dataList S k).lo : ℤ) = ((abData S hA).data k).lo + (vN S : ℤ) := by omega
      omega
    have h2 : (dataList S k).lo ≤ 2 * vN S - 1 := by
      have : ((dataList S k).lo : ℤ) = ((abData S hA).data k).lo + (vN S : ℤ) := by omega
      omega
    rw [show min (max (dataList S k).lo 1) (2 * vN S - 1) = (dataList S k).lo by omega]
    omega
  · have hget : (abSpecData S).IloRaw.getD k (vN S) = vN S := by
      simp only [abSpecData, getD_map_range]
      rw [if_neg (by omega)]
    rw [hget, (data_out S (by omega) hA).2.2.1]
    rw [show min (max (vN S) 1) (2 * vN S - 1) = vN S by omega]
    omega

include hA in
lemma abSpecData_Imax (k : ℕ) :
    (abSpecData S).toGapSpec.Imax k = ((abData S hA).data k).hi := by
  have hv := abSpecData_v S
  have hvpos := one_le_vN S
  have hint := (abData S hA).data_interval k
  have hvz : (abData S hA).vz = (vN S : ℤ) := rfl
  rw [hvz] at hint
  have hmin := abSpecData_Imin S hA k
  simp only [GapSpecData.toGapSpec_Imin, GapSpecData.ilo, hv] at hmin
  simp only [GapSpecData.toGapSpec_Imax, GapSpecData.ihi, GapSpecData.ilo, hv]
  by_cases hk : k ≤ sN S
  · have hhi := (dataList_agrees S hA k).2.2.2
    have hlo := (dataList_agrees S hA k).2.2.1
    have hgetl : (abSpecData S).IloRaw.getD k (vN S) = (dataList S k).lo := by
      simp only [abSpecData, getD_map_range]
      rw [if_pos (by omega)]
    have hget : (abSpecData S).IhiRaw.getD k (vN S) = (dataList S k).hi := by
      simp only [abSpecData, getD_map_range]
      rw [if_pos (by omega)]
    rw [hget, hgetl]
    have h1 : 1 ≤ (dataList S k).hi := by
      have : ((dataList S k).hi : ℤ) = ((abData S hA).data k).hi + (vN S : ℤ) := by omega
      omega
    have h2 : (dataList S k).hi ≤ 2 * vN S - 1 := by
      have : ((dataList S k).hi : ℤ) = ((abData S hA).data k).hi + (vN S : ℤ) := by omega
      omega
    have h3 : (dataList S k).lo ≤ (dataList S k).hi := by
      have e1 : ((dataList S k).lo : ℤ) = ((abData S hA).data k).lo + (vN S : ℤ) := by omega
      have e2 : ((dataList S k).hi : ℤ) = ((abData S hA).data k).hi + (vN S : ℤ) := by omega
      omega
    rw [show min (max (dataList S k).hi 1) (2 * vN S - 1) = (dataList S k).hi by omega,
      show min (max (dataList S k).lo 1) (2 * vN S - 1) = (dataList S k).lo by omega,
      show max (dataList S k).lo (dataList S k).hi = (dataList S k).hi by omega]
    omega
  · have hget : (abSpecData S).IhiRaw.getD k (vN S) = vN S := by
      simp only [abSpecData, getD_map_range]
      rw [if_neg (by omega)]
    have hgetl : (abSpecData S).IloRaw.getD k (vN S) = vN S := by
      simp only [abSpecData, getD_map_range]
      rw [if_neg (by omega)]
    rw [hget, hgetl, (data_out S (by omega) hA).2.2.2]
    rw [show min (max (vN S) 1) (2 * vN S - 1) = vN S by omega]
    simp

include hA in
/-- **The finite specification is the specification of the paper.**  Reading the finite data
`abSpecData S` as a `GapSpec` gives exactly the specification `(abData S hA).spec` that
Sections 2.6–2.8 attach to the AB tile set `S`. -/
theorem abSpecData_toGapSpec : (abSpecData S).toGapSpec = (abData S hA).spec := by
  refine GapSpec.ext' ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [GapSpecData.toGapSpec_s, abSpecData_s]
    rfl
  · simp only [GapSpecData.toGapSpec_v, abSpecData_v]
    rfl
  · funext k
    exact abSpecData_L S hA k
  · funext k
    exact abSpecData_R S hA k
  · funext k
    exact abSpecData_Imin S hA k
  · funext k
    exact abSpecData_Imax S hA k

end ABSim

end StickPolyhex
