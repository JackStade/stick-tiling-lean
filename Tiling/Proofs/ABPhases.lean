import Tiling.Proofs.ABGadgets

/-!
# Reading the bucket table

The buckets of `ABData.data` are grouped into gadgets; this file records which bucket carries
which data, in the form used by the two directions of the proof.  A *phase* `j` is the index of a
bucket counted from `0`, so that the bucket `j + 1` of the table is the one reached after `j`
steps down from an encoding row.
-/

namespace StickPolyhex

namespace ABSim

namespace ABData

variable (D : ABData)

/-! ### The length of the cycle -/

lemma sN_even : D.sN % 2 = 0 := by unfold sN; omega

lemma sixteen_le_sN : 16 ≤ D.sN := by unfold sN; omega

/-! ### The buckets of a matching gadget -/

@[simp] lemma matchData_one (g : ℤ → ℤ) :
    D.matchData g 1 = ⟨D.Efull, D.Rload g, 0, 6 * D.kz⟩ := rfl

@[simp] lemma matchData_two (g : ℤ → ℤ) :
    D.matchData g 2 = ⟨D.Eset, D.Aset, 0, 6 * D.kz⟩ := rfl

@[simp] lemma matchData_three (g : ℤ → ℤ) :
    D.matchData g 3 = ⟨D.Efull, D.Rreset, 0, 6 * D.kz⟩ := rfl

@[simp] lemma matchData_four (g : ℤ → ℤ) :
    D.matchData g 4 = ⟨D.Eset, D.Eset, 0, 6 * D.kz⟩ := rfl

/-! ### The buckets of a free gadget -/

lemma freeData₁_odd (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    D.freeData₁ (2 * p - 1) = ⟨D.Efull, D.C₁ (p : ℤ), -D.d + 1, 1⟩ := by
  unfold freeData₁
  rw [if_pos (by omega), if_pos (by omega)]
  congr 2
  omega

lemma freeData₁_even (p : ℕ) (h2 : p ≤ D.P) :
    D.freeData₁ (2 * p) = ⟨D.C₁ (p : ℤ), D.Efull, 0, 0⟩ := by
  unfold freeData₁
  rw [if_pos (by omega), if_neg (by omega)]
  congr 2
  omega

lemma freeData₁_exp_odd (p : ℕ) (h1 : 1 ≤ p) :
    D.freeData₁ (2 * D.P + 2 * p - 1) = ⟨D.Efull, D.D₁ (p : ℤ), -1, D.d - 1⟩ := by
  unfold freeData₁
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2
  omega

lemma freeData₁_exp_even (p : ℕ) (h1 : 1 ≤ p) (h2 : p < D.P) :
    D.freeData₁ (2 * D.P + 2 * p) = ⟨D.D₁ (p : ℤ), D.Efull, 0, 0⟩ := by
  unfold freeData₁
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 2
  omega

lemma freeData₁_last :
    D.freeData₁ (4 * D.P) = ⟨D.D₁ (D.P : ℤ), D.Eset, 0, 0⟩ := by
  have hp : 1 ≤ D.P := by unfold P; omega
  unfold freeData₁
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 2
  omega

lemma freeData₂_odd (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    D.freeData₂ (2 * p - 1) = ⟨D.Efull, D.C₂ (p : ℤ), -1, D.d - 1⟩ := by
  unfold freeData₂
  rw [if_pos (by omega), if_pos (by omega)]
  congr 2
  omega

lemma freeData₂_even (p : ℕ) (h2 : p ≤ D.P) :
    D.freeData₂ (2 * p) = ⟨D.C₂ (p : ℤ), D.Efull, 0, 0⟩ := by
  unfold freeData₂
  rw [if_pos (by omega), if_neg (by omega)]
  congr 2
  omega

lemma freeData₂_exp_odd (p : ℕ) (h1 : 1 ≤ p) :
    D.freeData₂ (2 * D.P + 2 * p - 1) = ⟨D.Efull, D.D₂ (p : ℤ), -D.d + 1, 1⟩ := by
  unfold freeData₂
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2
  omega

lemma freeData₂_exp_even (p : ℕ) (h1 : 1 ≤ p) :
    D.freeData₂ (2 * D.P + 2 * p) = ⟨D.D₂ (p : ℤ), D.Efull, 0, 0⟩ := by
  unfold freeData₂
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2
  omega

/-! ### Where each gadget sits in the table -/

lemma data_one : D.data 1 = ⟨D.Eset, D.Eset, 0, 0⟩ := by
  unfold data
  rw [if_pos rfl]

lemma data_m1 (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    D.data (1 + i) = D.matchData D.g₁ i := by
  unfold data
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma data_m2 (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    D.data (5 + i) = D.matchData D.g₂ i := by
  unfold data
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma data_f1 (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 4 * D.P) :
    D.data (9 + i) = D.freeData₁ i := by
  unfold data
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma data_m3 (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    D.data (9 + 4 * D.P + i) = D.matchData D.g₃ i := by
  unfold data
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  congr 1
  omega

lemma data_m4 (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    D.data (13 + 4 * D.P + i) = D.matchData D.g₄ i := by
  unfold data
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma data_f2 (i : ℕ) (h1 : 1 ≤ i) (h2 : i < 4 * D.P) :
    D.data (17 + 4 * D.P + i) = D.freeData₂ i := by
  have : D.sN = 16 + 8 * D.P := rfl
  unfold data
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

end ABData

end ABSim

end StickPolyhex
