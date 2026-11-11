import Tiling.Proofs.ABValueLists

/-!
# The bucket table of an AB tile set, as finite data

`ABSim.ABData.data` is the table of the `s` buckets of Sections 2.6–2.8: for each bucket it gives
the set of allowed left values, the set of allowed right values and the two ends of the interval.
This file mirrors that table by `ABSim.dataList`, which gives the same information as lists of
natural numbers (the two ends of the interval being shifted by `v`, so that they too are natural
numbers), and proves that the two tables agree bucket by bucket.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB

variable (S : ABTileSet) (hA : S.A ≠ [])

/-- The data of one bucket, in finite form: the lists of allowed left and right values, and the
two ends of the interval shifted by `v`. -/
structure BucketData where
  /-- The allowed left values. -/
  L : List ℕ
  /-- The allowed right values. -/
  R : List ℕ
  /-- The left end of the interval, shifted by `v`. -/
  lo : ℕ
  /-- The right end of the interval, shifted by `v`. -/
  hi : ℕ

/-- The four buckets of a matching gadget with load function `gN`. -/
def matchList (gN : ℕ → ℕ) (i : ℕ) : BucketData :=
  if i = 1 then ⟨EfullL S, RloadL S gN, vN S, vN S + 6 * kN S⟩
  else if i = 2 then ⟨EsetL S, AsetL S, vN S, vN S + 6 * kN S⟩
  else if i = 3 then ⟨EfullL S, RresetL S, vN S, vN S + 6 * kN S⟩
  else ⟨EsetL S, EsetL S, vN S, vN S + 6 * kN S⟩

/-- The buckets of the first free gadget. -/
def freeList₁ (i : ℕ) : BucketData :=
  if i ≤ 2 * pN S then
    (if i % 2 = 1 then ⟨EfullL S, C₁L S ((i + 1) / 2), vN S - dN S + 1, vN S + 1⟩
     else ⟨C₁L S (i / 2), EfullL S, vN S, vN S⟩)
  else
    (if (i - 2 * pN S) % 2 = 1 then
        ⟨EfullL S, D₁L S ((i - 2 * pN S + 1) / 2), vN S - 1, vN S + dN S - 1⟩
     else ⟨D₁L S ((i - 2 * pN S) / 2),
            (if i = 4 * pN S then EsetL S else EfullL S), vN S, vN S⟩)

/-- The buckets of the second free gadget. -/
def freeList₂ (i : ℕ) : BucketData :=
  if i ≤ 2 * pN S then
    (if i % 2 = 1 then ⟨EfullL S, C₂L S ((i + 1) / 2), vN S - 1, vN S + dN S - 1⟩
     else ⟨C₂L S (i / 2), EfullL S, vN S, vN S⟩)
  else
    (if (i - 2 * pN S) % 2 = 1 then
        ⟨EfullL S, D₂L S ((i - 2 * pN S + 1) / 2), vN S - dN S + 1, vN S + 1⟩
     else ⟨D₂L S ((i - 2 * pN S) / 2), EfullL S, vN S, vN S⟩)

/-- The table of the `s` buckets, in finite form. -/
def dataList (q : ℕ) : BucketData :=
  if q = 1 then ⟨EsetL S, EsetL S, vN S, vN S⟩
  else if q ≤ 5 then matchList S (g₁N S) (q - 1)
  else if q ≤ 9 then matchList S (g₂N S) (q - 5)
  else if q ≤ 9 + 4 * pN S then freeList₁ S (q - 9)
  else if q ≤ 13 + 4 * pN S then matchList S (g₃N S) (q - 9 - 4 * pN S)
  else if q ≤ 17 + 4 * pN S then matchList S (g₄N S) (q - 13 - 4 * pN S)
  else if q ≤ sN S then freeList₂ S (q - 17 - 4 * pN S)
  else ⟨[], [], vN S, vN S⟩

/-! ## The finite table agrees with the table of the construction -/

lemma dN_le_vN : dN S ≤ vN S := by
  have := vN_eq S
  omega

lemma six_kN_le_vN : 6 * kN S ≤ vN S := by
  have h1 := vN_eq S
  have h2 := twelve_kN_le_dN S
  omega

include hA in
lemma matchList_agrees {gN : ℕ → ℕ} {g : ℤ → ℤ}
    (hcast : ∀ l : ℕ, 1 ≤ l → ((gN l : ℕ) : ℤ) = g (l : ℤ))
    (hb : ∀ l : ℕ, gN l ≤ 5 * kN S - 1) (i : ℕ) :
    ListsSet (vN S) (matchList S gN i).L ((abData S hA).matchData g i).L ∧
      ListsSet (vN S) (matchList S gN i).R ((abData S hA).matchData g i).R ∧
      (((matchList S gN i).lo : ℤ) - (vN S : ℤ) = ((abData S hA).matchData g i).lo) ∧
      (((matchList S gN i).hi : ℤ) - (vN S : ℤ) = ((abData S hA).matchData g i).hi) := by
  have hv := six_kN_le_vN S
  have hE := listsSet_EfullL S hA
  have hEs := listsSet_EsetL S hA
  have hR := listsSet_RloadL S hA hcast hb
  have hRreset := listsSet_RresetL S hA
  have hAs := listsSet_AsetL S hA
  simp only [matchList, ABData.matchData, abData_kz]
  split_ifs <;>
    refine ⟨by assumption, by assumption, by push_cast; omega, by push_cast; omega⟩

include hA in
lemma freeList₁_agrees (i : ℕ) :
    ListsSet (vN S) (freeList₁ S i).L ((abData S hA).freeData₁ i).L ∧
      ListsSet (vN S) (freeList₁ S i).R ((abData S hA).freeData₁ i).R ∧
      (((freeList₁ S i).lo : ℤ) - (vN S : ℤ) = ((abData S hA).freeData₁ i).lo) ∧
      (((freeList₁ S i).hi : ℤ) - (vN S : ℤ) = ((abData S hA).freeData₁ i).hi) := by
  have hv := dN_le_vN S
  have hd : 1 ≤ dN S := by have := twelve_kN_le_dN S; have := one_le_kN S; omega
  have hE := listsSet_EfullL S hA
  have hEs := listsSet_EsetL S hA
  have hC := listsSet_C₁L S hA
  have hD := listsSet_D₁L S hA
  simp only [freeList₁, ABData.freeData₁, abData_P, abData_d]
  split_ifs <;>
    refine ⟨by first | assumption | apply hC | apply hD,
      by first | assumption | apply hC | apply hD, by push_cast; omega, by push_cast; omega⟩

include hA in
lemma freeList₂_agrees (i : ℕ) :
    ListsSet (vN S) (freeList₂ S i).L ((abData S hA).freeData₂ i).L ∧
      ListsSet (vN S) (freeList₂ S i).R ((abData S hA).freeData₂ i).R ∧
      (((freeList₂ S i).lo : ℤ) - (vN S : ℤ) = ((abData S hA).freeData₂ i).lo) ∧
      (((freeList₂ S i).hi : ℤ) - (vN S : ℤ) = ((abData S hA).freeData₂ i).hi) := by
  have hv := dN_le_vN S
  have hd : 1 ≤ dN S := by have := twelve_kN_le_dN S; have := one_le_kN S; omega
  have hE := listsSet_EfullL S hA
  have hEs := listsSet_EsetL S hA
  have hC := listsSet_C₂L S hA
  have hD := listsSet_D₂L S hA
  simp only [freeList₂, ABData.freeData₂, abData_P, abData_d]
  split_ifs <;>
    refine ⟨by first | assumption | apply hC | apply hD,
      by first | assumption | apply hC | apply hD, by push_cast; omega, by push_cast; omega⟩

include hA in
/-- **The finite bucket table agrees with the table of the construction.** -/
theorem dataList_agrees (q : ℕ) :
    ListsSet (vN S) (dataList S q).L ((abData S hA).data q).L ∧
      ListsSet (vN S) (dataList S q).R ((abData S hA).data q).R ∧
      (((dataList S q).lo : ℤ) - (vN S : ℤ) = ((abData S hA).data q).lo) ∧
      (((dataList S q).hi : ℤ) - (vN S : ℤ) = ((abData S hA).data q).hi) := by
  have hEs := listsSet_EsetL S hA
  have h1 := matchList_agrees S hA (fun _ hl => g₁N_eq S hA hl) (g₁N_lt S)
  have h2 := matchList_agrees S hA (fun _ hl => g₂N_eq S hA hl) (g₂N_lt S)
  have h3 := matchList_agrees S hA (fun _ hl => g₃N_eq S hA hl) (g₃N_lt S)
  have h4 := matchList_agrees S hA (fun _ hl => g₄N_eq S hA hl) (g₄N_lt S)
  have hf1 := freeList₁_agrees S hA
  have hf2 := freeList₂_agrees S hA
  simp only [dataList, ABData.data, abData_P, abData_sN]
  split_ifs
  · exact ⟨hEs, hEs, by push_cast; ring, by push_cast; ring⟩
  · exact h1 _
  · exact h2 _
  · exact hf1 _
  · exact h3 _
  · exact h4 _
  · exact hf2 _
  · exact ⟨listsSet_nil (fun _ hx => hx), listsSet_nil (fun _ hx => hx), by push_cast; ring,
      by push_cast; ring⟩

end ABSim

end StickPolyhex
