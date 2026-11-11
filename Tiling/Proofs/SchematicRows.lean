import Tiling.Proofs.Schematic

/-!
# Rows of a schematic

This file collects the combinatorial facts about a single row of a schematic and about two
adjacent rows that are needed to show that the tiling described by a schematic forms a weave
pattern.

The main results are:

* `Schematic.start_unique`: a column belongs to at most one block, so a block is determined by
  any of its columns;
* `Schematic.isGap_between`: two gap columns at distance at most `n + 1` belong to the same gap
  (there is no room for a whole block between them);
* `Schematic.blockStart_eq_or`: a window of columns of length at most `2 * n + 2` meets at most
  two blocks;
* `Schematic.exists_gap_of_range`: among any `n + 2` consecutive columns of a row there is a gap
  column;
* `Schematic.exists_gap_above_block`: above every block there is a gap of the next row, and it
  lies strictly inside the block;
* `Schematic.start_eq_of_no_gap`: consecutive columns with no gap between them belong to one
  block.
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-! ### Blocks described by their leftmost column -/

/-- The slot of a column of a block, described from the leftmost column of the block. -/
lemma slot_of_start {r s y : ℤ} (h : S.slot r s = .block 0) (h1 : s ≤ y) (h2 : y ≤ s + n) :
    S.slot r y = .block (y - s).toNat := by
  have hk : (y - s).toNat ≤ n := by omega
  have hb := S.slot_block_of_block (r := r) (x := s) (j := 0) h hk
  rwa [show s - ((0 : ℕ) : ℤ) + (((y - s).toNat : ℕ) : ℤ) = y by omega] at hb

/-- A column belongs to at most one block. -/
lemma start_unique {r a b y : ℤ} (ha : S.slot r a = .block 0) (hb : S.slot r b = .block 0)
    (h1 : a ≤ y) (h2 : y ≤ a + n) (h3 : b ≤ y) (h4 : y ≤ b + n) : a = b := by
  have e1 := S.slot_of_start ha h1 h2
  have e2 := S.slot_of_start hb h3 h4
  rw [e1] at e2
  injection e2 with e
  omega

lemma exists_block_of_not_isGap {r y : ℤ} (h : ¬ (S.slot r y).IsGap) :
    ∃ j, S.slot r y = .block j := by
  cases hh : S.slot r y with
  | block j => exact ⟨j, rfl⟩
  | gapL => rw [hh] at h; exact absurd trivial h
  | gapR => rw [hh] at h; exact absurd trivial h

/-! ### Gaps -/

/-- Two gap columns at distance at most `n + 1` belong to one gap: a whole block does not fit
between them. -/
lemma isGap_between {r g1 g2 y : ℤ} (h1 : (S.slot r g1).IsGap) (h2 : (S.slot r g2).IsGap)
    (hy1 : g1 ≤ y) (hy2 : y ≤ g2) (hd : g2 - g1 ≤ n + 1) : (S.slot r y).IsGap := by
  by_contra hcon
  obtain ⟨j, hj⟩ := S.exists_block_of_not_isGap hcon
  have hjn := S.block_le hj
  have hstart := S.slot_block_zero hj
  have hg1 : g1 < y - (j : ℤ) := by
    by_contra hc
    push_neg at hc
    have hb := S.slot_of_start hstart hc (by omega)
    rw [hb] at h1
    exact h1
  have hg2 : y - (j : ℤ) + n < g2 := by
    by_contra hc
    push_neg at hc
    have hb := S.slot_of_start hstart (by omega) hc
    rw [hb] at h2
    exact h2
  omega

/-- A window of columns of length at most `2 * n + 2` meets at most two blocks. -/
lemma blockStart_eq_or {r s1 s2 s col : ℤ}
    (h1 : S.slot r s1 = .block 0) (h2 : S.slot r s2 = .block 0) (hs : S.slot r s = .block 0)
    (hc1 : s1 ≤ col) (hc2 : col ≤ s2 + n) (hcs : s ≤ col) (hcs' : col ≤ s + n)
    (hbound : s2 - s1 ≤ 2 * n + 1) : s = s1 ∨ s = s2 := by
  by_cases hA : col ≤ s1 + n
  · exact Or.inl (S.start_unique hs h1 hcs hcs' hc1 hA)
  by_cases hB : s2 ≤ col
  · exact Or.inr (S.start_unique hs h2 hcs hcs' hB hc2)
  push_neg at hA hB
  have hs1 : s1 + n < s := by
    by_contra hc
    push_neg at hc
    have := S.start_unique (y := s) hs h1 le_rfl (by omega) (by omega) hc
    omega
  have hs2 : s + n < s2 := by
    by_contra hc
    push_neg at hc
    have := S.start_unique (y := s2) hs h2 (by omega) hc le_rfl (by omega)
    omega
  omega

/-- Among any `n + 2` consecutive columns of a row there is a gap column. -/
lemma exists_gap_of_range (r y : ℤ) : ∃ k : ℕ, k ≤ n + 1 ∧ (S.slot r (y + k)).IsGap := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k : ℕ, k ≤ n + 1 → ∃ j, S.slot r (y + k) = .block j ∧ k ≤ j := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨j, hj⟩ := S.exists_block_of_not_isGap (hcon 0 (by omega))
      exact ⟨j, hj, Nat.zero_le _⟩
    | succ k ih =>
      intro hk
      obtain ⟨j, hj, hkj⟩ := ih (by omega)
      have hjn := S.block_le hj
      rcases lt_or_eq_of_le hjn with hlt | heq
      · refine ⟨j + 1, ?_, by omega⟩
        rw [show y + ((k + 1 : ℕ) : ℤ) = y + (k : ℤ) + 1 by push_cast; ring]
        exact S.step_of_block_lt hj hlt
      · exfalso
        have hgL : S.slot r (y + (k : ℤ) + 1) = .gapL := S.step_of_block_n (heq ▸ hj)
        have h2 := hcon (k + 1) hk
        rw [show y + ((k + 1 : ℕ) : ℤ) = y + (k : ℤ) + 1 by push_cast; ring, hgL] at h2
        exact h2 trivial
  obtain ⟨j, hj, hle⟩ := key (n + 1) le_rfl
  have := S.block_le hj
  omega

/-! ### Two adjacent rows -/

/-- A gap of the row above sits strictly inside a block: the columns of index `0`, `1` and `n`
of a block never carry a gap of the row above. -/
lemma not_isGap_above_of_block {r y : ℤ} {j : ℕ} (h : S.slot r y = .block j)
    (hj : j < 2 ∨ n ≤ j) : ¬ (S.slot (r + 1) y).IsGap := by
  intro hg
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r y hg
  rw [h] at hk
  injection hk with e
  omega

/-- A gap column never sits above a gap column. -/
lemma not_isGap_above_of_isGap {r y : ℤ} (h : (S.slot r y).IsGap) :
    ¬ (S.slot (r + 1) y).IsGap := by
  intro hg
  obtain ⟨k, -, -, hk⟩ := S.slot_overlap r y hg
  rw [hk] at h
  exact h

/-- Above every block there is a gap column of the next row, and it lies strictly inside the
block, at least two columns away from either end. -/
lemma exists_gap_above_block {r x0 : ℤ} (h : S.slot r x0 = .block 0) :
    ∃ g, x0 + 2 ≤ g ∧ g + 1 ≤ x0 + n ∧ (S.slot (r + 1) g).IsGap := by
  obtain ⟨k, hk, hgap⟩ := S.exists_gap_of_range (r + 1) x0
  obtain ⟨j, hj2, hjn, hj⟩ := S.slot_overlap r (x0 + k) hgap
  have hkn : (k : ℤ) ≤ n := by
    by_contra hc
    have hkk : (k : ℤ) = (n : ℤ) + 1 := by omega
    have hgL : S.slot r (x0 + (k : ℤ)) = .gapL := by
      rw [show x0 + (k : ℤ) = x0 - ((0 : ℕ) : ℤ) + n + 1 by push_cast; omega]
      exact S.gapL_of_block_n (j := 0) h
    rw [hgL] at hj
    exact Slot.noConfusion hj
  have hb := S.slot_of_start h (show x0 ≤ x0 + (k : ℤ) by omega) (by omega)
  rw [hb] at hj
  injection hj with e
  refine ⟨x0 + k, by omega, by omega, hgap⟩

/-- Consecutive columns with no gap between them belong to a single block. -/
lemma start_eq_of_no_gap {r y : ℤ} {jy : ℕ} (hy : S.slot r y = .block jy) (k : ℕ)
    (hg : ∀ i : ℕ, i ≤ k → ¬ (S.slot r (y + i)).IsGap) :
    ∃ j', S.slot r (y + k) = .block j' ∧ (y + k) - j' = y - jy := by
  induction k with
  | zero => exact ⟨jy, by simpa using hy, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj, hstart⟩ := ih (fun i hi => hg i (by omega))
    have hjn := S.block_le hj
    rcases lt_or_eq_of_le hjn with hlt | heq
    · refine ⟨j + 1, ?_, ?_⟩
      · rw [show y + ((k + 1 : ℕ) : ℤ) = y + (k : ℤ) + 1 by push_cast; ring]
        exact S.step_of_block_lt hj hlt
      · push_cast at hstart ⊢
        omega
    · exfalso
      have hgL : S.slot r (y + (k : ℤ) + 1) = .gapL := S.step_of_block_n (heq ▸ hj)
      have h2 := hg (k + 1) le_rfl
      rw [show y + ((k + 1 : ℕ) : ℤ) = y + (k : ℤ) + 1 by push_cast; ring, hgL] at h2
      exact h2 trivial

end Schematic

end StickPolyhex
