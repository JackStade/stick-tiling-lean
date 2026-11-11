import Tiling.Proofs.SchematicLabels

/-!
# Configurations that cannot occur in a schematic, and matched pairs of edges

This file collects the combinatorial facts about a schematic that are needed to enumerate the
pairs of matched edges of the tiling `S.toTiling`:

* which slots can lie directly above a given slot (`no_block_n_above_gap`,
  `no_block_zero_above_gap`, `block_add_two_le_of_block_n_above`, `not_gap_above_gap`);
* the same, one column to the right — the configuration met when climbing out of the top of a
  band in the direction `HexDir.NE` (`no_diag_gap_above_block_n`, `no_diag_block_zero_above_gap`,
  …).

It also records the reduction `StickTiling.satisfiesRules_of_three`: since the two edges of a
matched pair play symmetric roles, a tiling satisfies a set of edge-matching rules as soon as no
forbidden pair occurs on the edges in the three directions `E`, `NE`, `NW`.
-/

namespace StickPolyhex

namespace StickTiling

variable {N : ℕ} (T : StickTiling N) (R : EdgeRules N)

/-- To check a set of matching rules it suffices to check the edges in the three directions
`E`, `NE` and `NW`: the remaining three directions give the same matched pairs, in the opposite
order. -/
theorem satisfiesRules_of_three
    (h : ∀ (c : Hex) (e : HexDir) (p q : R.Label), e = HexDir.E ∨ e = HexDir.NE ∨ e = HexDir.NW →
      T.labelOf R c e = some p → T.labelOf R (nbr c e) e.opp = some q → ¬ R.Forbidden p q) :
    T.SatisfiesRules R := by
  intro c e p q hp hq hf
  have key : ∀ (d : HexDir), d = HexDir.E ∨ d = HexDir.NE ∨ d = HexDir.NW →
      e = d.opp → False := by
    rintro d hd rfl
    have h1 : T.labelOf R (nbr c d.opp) d = some q := by
      simpa using hq
    have h2 : T.labelOf R (nbr (nbr c d.opp) d) d.opp = some p := by
      simpa using hp
    exact h (nbr c d.opp) d q p hd h1 h2 (R.forbidden_symm hf)
  rcases HexDir.cases_six e with he | he | he | he | he | he
  · exact h c e p q (Or.inl he) hp hq hf
  · exact h c e p q (Or.inr (Or.inl he)) hp hq hf
  · exact h c e p q (Or.inr (Or.inr he)) hp hq hf
  · exact key HexDir.E (Or.inl rfl) (by rw [he]; decide)
  · exact key HexDir.NE (Or.inr (Or.inl rfl)) (by rw [he]; decide)
  · exact key HexDir.NW (Or.inr (Or.inr rfl)) (by rw [he]; decide)

end StickTiling

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-- Every cell is the cell of its column, at its height inside its band. -/
lemma exists_cellAt (c : Hex) : ∃ (r x : ℤ) (s : ℕ), s ≤ n ∧ c = cellAt n r x s := by
  refine ⟨bandRow n (shearRow c), shearCol c, (subRow n (shearRow c)).toNat, ?_, ?_⟩
  · have h1 := subRow_le n (shearRow c)
    have h0 := subRow_nonneg n (shearRow c)
    omega
  · have h0 := subRow_nonneg n (shearRow c)
    rw [show (((subRow n (shearRow c)).toNat : ℕ) : ℤ) = subRow n (shearRow c) by omega]
    exact (cellAt_bandOf n c).symm

/-! ### Which slots may lie above which -/

/-- A gap column lies above a block column that is neither the first nor the last two. -/
lemma block_bounds_of_gap_above {r x : ℤ} {j : ℕ} (hgap : (S.slot (r + 1) x).IsGap)
    (hb : S.slot r x = .block j) : 2 ≤ j ∧ j + 1 ≤ n := by
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r x hgap
  rw [hb] at hk
  injection hk with hk
  omega

/-- A gap column never lies above a gap column. -/
lemma not_gap_above_gap {r x : ℤ} (h : (S.slot r x).IsGap) (h' : (S.slot (r + 1) x).IsGap) :
    False := by
  obtain ⟨k, -, -, hk⟩ := S.slot_overlap r x h'
  rw [hk] at h
  exact h

/-- The last column of a block never lies above a gap column. -/
lemma no_block_n_above_gap {r x : ℤ} (h : (S.slot r x).IsGap) : S.slot (r + 1) x ≠ .block n := by
  intro hn
  have hgapL : S.slot (r + 1) (x + 1) = .gapL := S.step_of_block_n hn
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r (x + 1) (by rw [hgapL]; trivial)
  cases hs : S.slot r x with
  | block j => rw [hs] at h; exact h
  | gapL =>
    rcases S.succ_of_gapL hs with h1 | h1 <;> rw [h1] at hk <;> exact Slot.noConfusion hk
  | gapR =>
    rcases S.succ_of_gapR hs with h1 | h1
    · rw [h1] at hk; exact Slot.noConfusion hk
    · rw [h1] at hk; injection hk with hk; omega

/-- The first column of a block never lies above a gap column. -/
lemma no_block_zero_above_gap {r x : ℤ} (h : (S.slot r x).IsGap) :
    S.slot (r + 1) x ≠ .block 0 := by
  intro hn
  have hgapR : S.slot (r + 1) (x - 1) = .gapR := S.gapR_of_block_zero hn
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r (x - 1) (by rw [hgapR]; trivial)
  cases hs : S.slot r x with
  | block j => rw [hs] at h; exact h
  | gapL =>
    rcases S.pred_of_gapL (by rw [show x - 1 + 1 = x by ring]; exact hs) with h1 | h1
    · rw [h1] at hk; injection hk with hk; omega
    · rw [h1] at hk; exact Slot.noConfusion hk
  | gapR =>
    rcases S.pred_of_gapR (by rw [show x - 1 + 1 = x by ring]; exact hs) with h1 | h1 <;>
      rw [h1] at hk <;> exact Slot.noConfusion hk

/-- If the last column of a block lies above the `j`-th column of a block, then `1 ≤ j` and
`j + 2 ≤ n`. -/
lemma block_bounds_of_block_n_above {r x : ℤ} {j : ℕ} (hb : S.slot r x = .block j)
    (h' : S.slot (r + 1) x = .block n) : 1 ≤ j ∧ j + 2 ≤ n := by
  have hgapL : S.slot (r + 1) (x + 1) = .gapL := S.step_of_block_n h'
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r (x + 1) (by rw [hgapL]; trivial)
  rcases eq_or_lt_of_le (S.block_le hb) with rfl | hlt
  · rw [S.step_of_block_n hb] at hk; exact Slot.noConfusion hk
  · rw [S.step_of_block_lt hb hlt] at hk
    injection hk with hk
    omega

/-! ### The same, one column to the right -/

/-- No gap column lies above and to the right of the last column of a block. -/
lemma no_diag_gap_above_block_n {r x : ℤ} (hb : S.slot r x = .block n) :
    ¬ (S.slot (r + 1) (x + 1)).IsGap := by
  intro hgap
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r (x + 1) hgap
  rw [S.step_of_block_n hb] at hk
  exact Slot.noConfusion hk

/-- No first column of a block lies above and to the right of the last column of a block. -/
lemma no_diag_block_zero_above_block_n {r x : ℤ} (hb : S.slot r x = .block n) :
    S.slot (r + 1) (x + 1) ≠ .block 0 := by
  intro h0
  have hgapR : S.slot (r + 1) x = .gapR := by
    have := S.gapR_of_block_zero h0
    rwa [show x + 1 - 1 = x by ring] at this
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r x (by rw [hgapR]; trivial)
  rw [hb] at hk
  injection hk with hk
  omega

/-- No gap column lies above and to the right of a gap column. -/
lemma no_diag_gap_above_gap {r x : ℤ} (h : (S.slot r x).IsGap) :
    ¬ (S.slot (r + 1) (x + 1)).IsGap := by
  intro hgap
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap r (x + 1) hgap
  cases hs : S.slot r x with
  | block j => rw [hs] at h; exact h
  | gapL =>
    rcases S.succ_of_gapL hs with h1 | h1 <;> rw [h1] at hk <;> exact Slot.noConfusion hk
  | gapR =>
    rcases S.succ_of_gapR hs with h1 | h1
    · rw [h1] at hk; exact Slot.noConfusion hk
    · rw [h1] at hk; injection hk with hk; omega

/-- No first column of a block lies above and to the right of a gap column. -/
lemma no_diag_block_zero_above_gap {r x : ℤ} (h : (S.slot r x).IsGap) :
    S.slot (r + 1) (x + 1) ≠ .block 0 := by
  intro h0
  have hgapR : S.slot (r + 1) x = .gapR := by
    have := S.gapR_of_block_zero h0
    rwa [show x + 1 - 1 = x by ring] at this
  obtain ⟨k, -, -, hk⟩ := S.slot_overlap r x (by rw [hgapR]; trivial)
  rw [hk] at h
  exact h

end Schematic

end StickPolyhex
