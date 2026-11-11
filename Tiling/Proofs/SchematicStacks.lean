import Tiling.Proofs.SchematicSticks

/-!
# The stacks of the tiling described by a schematic

The stacks of `Schematic.toTiling` are exactly the blocks and the gaps of the schematic:

* the stack of a cell of a block consists of the `n + 1` horizontal sticks filling that block
  (the cells of the band of `c` lying in the columns of the block);
* the stack of a cell of a gap consists of the left-slanting sticks filling the columns of that
  gap.

This is the content of `Schematic.sameStack_iff`, which characterises
`StickTiling.SameStack` for the tiling of a schematic in terms of the relation
`Schematic.SameStackData`.  The main intermediate step is the identification of all the stacked
pairs of the tiling (`Schematic.stackedBy_NW`, `Schematic.stackedBy_SE`,
`Schematic.stackedBy_E`, `Schematic.stackedBy_W` and, conversely,
`Schematic.sameStackData_of_stackedBy`).
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-! ### Blocks in adjacent rows are never aligned -/

/-- Two blocks in adjacent rows never start in the same column. -/
lemma no_block_zero_above {r x : ℤ} (h : S.slot r x = .block 0) : S.slot (r + 1) x ≠ .block 0 := by
  intro h'
  have hgap : S.slot (r + 1) (x - 1) = .gapR := S.gapR_of_block_zero h'
  obtain ⟨j, hj2, hjn, hj⟩ := S.slot_overlap r (x - 1) (by rw [hgap]; trivial)
  rw [S.gapR_of_block_zero h] at hj
  exact Slot.noConfusion hj

/-- A block in a row never starts one column to the right of a block in the row below. -/
lemma no_block_zero_above_succ {r x : ℤ} (h : S.slot r x = .block 0) :
    S.slot (r + 1) (x + 1) ≠ .block 0 := by
  intro h'
  have hgap : S.slot (r + 1) x = .gapR := by
    have := S.gapR_of_block_zero h'
    rwa [show x + 1 - 1 = x by ring] at this
  obtain ⟨j, hj2, hjn, hj⟩ := S.slot_overlap r x (by rw [hgap]; trivial)
  rw [h] at hj
  injection hj with e
  omega

/-- Two blocks in adjacent rows never start in the same column (seen from the upper row). -/
lemma no_block_zero_below {r x : ℤ} (h : S.slot r x = .block 0) :
    S.slot (r - 1) x ≠ .block 0 := by
  intro h'
  have hgap : S.slot r (x - 1) = .gapR := S.gapR_of_block_zero h
  obtain ⟨j, hj2, hjn, hj⟩ := S.slot_overlap (r - 1) (x - 1) (by
    rw [show r - 1 + 1 = r by ring, hgap]; trivial)
  rw [S.gapR_of_block_zero h'] at hj
  exact Slot.noConfusion hj

/-- A block in a row never starts one column to the left of a block in the row above. -/
lemma no_block_zero_below_pred {r x : ℤ} (h : S.slot r x = .block 0) :
    S.slot (r - 1) (x - 1) ≠ .block 0 := by
  intro h'
  -- the block of the row `r - 1` ends at the column `x + n - 1`
  have hgapL : S.slot (r - 1) (x + n) = .gapL := by
    rw [show x + (n : ℤ) = x - 1 - ((0 : ℕ) : ℤ) + n + 1 by push_cast; ring]
    exact S.gapL_of_block_n (r := r - 1) (x := x - 1) (j := 0) h' 
  have hgap' : (S.slot (r - 1) (x + n + 1)).IsGap := by
    rcases S.succ_of_gapL hgapL with h1 | h1 <;> rw [h1] <;> trivial
  -- but the column `x + n + 1` of the row `r` is a gap column, forcing a block below it
  have hgapR : S.slot r (x + n + 1) = .gapL := by
    rw [show x + (n : ℤ) + 1 = x - ((0 : ℕ) : ℤ) + n + 1 by push_cast; ring]
    exact S.gapL_of_block_n (r := r) (x := x) (j := 0) h
  obtain ⟨j, hj2, hjn, hj⟩ := S.slot_overlap (r - 1) (x + n + 1) (by
    rw [show r - 1 + 1 = r by ring, hgapR]; trivial)
  rw [hj] at hgap'
  exact hgap'.elim

/-! ### The direction of a cell -/

lemma dirAt_cases (c : Hex) :
    (∃ j, S.slotAt c = .block j ∧ S.dirAt c = HexDir.W) ∨
      (S.slotAt c = .gapL ∧ S.dirAt c = HexDir.SE) ∨
      (S.slotAt c = .gapR ∧ S.dirAt c = HexDir.NW) := by
  cases h : S.slotAt c with
  | block j => exact Or.inl ⟨j, rfl, S.dirAt_block h⟩
  | gapL => exact Or.inr (Or.inl ⟨rfl, S.dirAt_gapL h⟩)
  | gapR => exact Or.inr (Or.inr ⟨rfl, S.dirAt_gapR h⟩)

lemma isGap_of_dirAt_ne_W {c : Hex} (h : S.dirAt c ≠ HexDir.W) : (S.slotAt c).IsGap := by
  rcases S.dirAt_cases c with ⟨j, hj, hd⟩ | ⟨hs, -⟩ | ⟨hs, -⟩
  · exact absurd hd h
  · rw [hs]; trivial
  · rw [hs]; trivial

lemma exists_block_of_dirAt_W {c : Hex} (h : S.dirAt c = HexDir.W) : ∃ j, S.slotAt c = .block j := by
  rcases S.dirAt_cases c with ⟨j, hj, -⟩ | ⟨hs, hd⟩ | ⟨hs, hd⟩
  · exact ⟨j, hj⟩
  · rw [hd] at h; exact absurd h (by decide)
  · rw [hd] at h; exact absurd h (by decide)

/-! ### The ends of a stick -/

lemma left_mem_stickOf {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    shearCell (shearCol c - j) (shearRow c) ∈ S.toTiling.stickOf c := by
  rw [S.mem_stickOf_block_iff h]
  simp

lemma right_mem_stickOf {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    shearCell (shearCol c - j + n) (shearRow c) ∈ S.toTiling.stickOf c := by
  rw [S.mem_stickOf_block_iff h]
  simp

lemma bot_mem_stickOf {c : Hex} (h : (S.slotAt c).IsGap) :
    shearCell (shearCol c) (((n : ℤ) + 1) * S.bandOf c) ∈ S.toTiling.stickOf c := by
  rw [S.mem_stickOf_gap_iff h]
  refine ⟨by simp, ?_⟩
  rw [bandOf_shearCell, show ((n : ℤ) + 1) * S.bandOf c = ((n : ℤ) + 1) * S.bandOf c + 0 by ring,
    bandRow_eq n _ _ le_rfl (by positivity)]

lemma top_mem_stickOf {c : Hex} (h : (S.slotAt c).IsGap) :
    shearCell (shearCol c) (((n : ℤ) + 1) * S.bandOf c + n) ∈ S.toTiling.stickOf c := by
  rw [S.mem_stickOf_gap_iff h]
  refine ⟨by simp, ?_⟩
  rw [bandOf_shearCell, bandRow_eq n _ _ (by positivity) le_rfl]

/-! ### The stacked pairs of the tiling -/

/-- Two horizontal sticks of one block, one directly above the other, form a stacked pair. -/
lemma stackedBy_NW {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) (hs : S.subOf c < n) :
    S.toTiling.StackedBy c (nbr c HexDir.NW) HexDir.NW := by
  have hnbr : S.slotAt (nbr c HexDir.NW) = .block j := by rw [S.slotAt_nbr_NW hs, h]
  refine ⟨?_, ?_, ?_⟩
  · rw [toTiling_dir, S.dirAt_block h]; decide
  · rw [toTiling_dir, toTiling_dir, S.dirAt_block h, S.dirAt_block hnbr]
    exact Or.inl rfl
  · intro x hx
    rw [S.mem_stickOf_block_iff h] at hx
    rw [S.mem_stickOf_block_iff hnbr, shearCol_nbr_NW, shearRow_nbr_NW, shearCol_nbr_NW,
      shearRow_nbr_NW]
    exact ⟨by omega, hx.2.1, hx.2.2⟩

/-- Two horizontal sticks of one block, one directly below the other, form a stacked pair. -/
lemma stackedBy_SE {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) (hs : 0 < S.subOf c) :
    S.toTiling.StackedBy c (nbr c HexDir.SE) HexDir.SE := by
  have hnbr : S.slotAt (nbr c HexDir.SE) = .block j := by rw [S.slotAt_nbr_SE hs, h]
  refine ⟨?_, ?_, ?_⟩
  · rw [toTiling_dir, S.dirAt_block h]; decide
  · rw [toTiling_dir, toTiling_dir, S.dirAt_block h, S.dirAt_block hnbr]
    exact Or.inl rfl
  · intro x hx
    rw [S.mem_stickOf_block_iff h] at hx
    rw [S.mem_stickOf_block_iff hnbr, shearCol_nbr_SE, shearRow_nbr_SE, shearCol_nbr_SE,
      shearRow_nbr_SE]
    exact ⟨by omega, hx.2.1, hx.2.2⟩

/-- Two left-slanting sticks in neighbouring columns of one gap form a stacked pair. -/
lemma stackedBy_E {c : Hex} (h : (S.slotAt c).IsGap) (h' : (S.slotAt (nbr c HexDir.E)).IsGap) :
    S.toTiling.StackedBy c (nbr c HexDir.E) HexDir.E := by
  have hband : S.bandOf (nbr c HexDir.E) = S.bandOf c := S.bandOf_congr (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rcases S.dirAt_cases c with ⟨j, hj, -⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
    · rw [hj] at h; exact h.elim
    · rw [toTiling_dir, hd]; decide
    · rw [toTiling_dir, hd]; decide
  · rcases S.dirAt_cases c with ⟨j, hj, -⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
    · rw [hj] at h; exact h.elim
    all_goals
      rcases S.dirAt_cases (nbr c HexDir.E) with ⟨j', hj', -⟩ | ⟨-, hd'⟩ | ⟨-, hd'⟩
      · rw [hj'] at h'; exact h'.elim
      all_goals rw [toTiling_dir, toTiling_dir, hd, hd']; first | exact Or.inl rfl | exact Or.inr rfl
  · intro x hx
    rw [S.mem_stickOf_gap_iff h] at hx
    rw [S.mem_stickOf_gap_iff h', shearCol_nbr_E, shearCol_nbr_E, hband,
      S.bandOf_congr (show shearRow (nbr x HexDir.E) = shearRow x by simp)]
    exact ⟨by omega, hx.2⟩

/-- Two left-slanting sticks in neighbouring columns of one gap form a stacked pair. -/
lemma stackedBy_W {c : Hex} (h : (S.slotAt c).IsGap) (h' : (S.slotAt (nbr c HexDir.W)).IsGap) :
    S.toTiling.StackedBy c (nbr c HexDir.W) HexDir.W := by
  have hband : S.bandOf (nbr c HexDir.W) = S.bandOf c := S.bandOf_congr (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rcases S.dirAt_cases c with ⟨j, hj, -⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
    · rw [hj] at h; exact h.elim
    · rw [toTiling_dir, hd]; decide
    · rw [toTiling_dir, hd]; decide
  · rcases S.dirAt_cases c with ⟨j, hj, -⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
    · rw [hj] at h; exact h.elim
    all_goals
      rcases S.dirAt_cases (nbr c HexDir.W) with ⟨j', hj', -⟩ | ⟨-, hd'⟩ | ⟨-, hd'⟩
      · rw [hj'] at h'; exact h'.elim
      all_goals rw [toTiling_dir, toTiling_dir, hd, hd']; first | exact Or.inl rfl | exact Or.inr rfl
  · intro x hx
    rw [S.mem_stickOf_gap_iff h] at hx
    rw [S.mem_stickOf_gap_iff h', shearCol_nbr_W, shearCol_nbr_W, hband,
      S.bandOf_congr (show shearRow (nbr x HexDir.W) = shearRow x by simp)]
    exact ⟨by omega, hx.2⟩

/-! ### Lying in the same stack -/

/-- Two cells lie in the same stack of the tiling of the schematic: either they are cells of
blocks of one row of the schematic with the same left end, or they are gap cells of one row with
only gap columns between them. -/
def SameStackData (a b : Hex) : Prop :=
  (∃ ja jb, S.slotAt a = .block ja ∧ S.slotAt b = .block jb ∧ S.bandOf a = S.bandOf b ∧
      shearCol a - ja = shearCol b - jb) ∨
    ((S.slotAt a).IsGap ∧ (S.slotAt b).IsGap ∧ S.bandOf a = S.bandOf b ∧
      ∀ y : ℤ, ((shearCol a ≤ y ∧ y ≤ shearCol b) ∨ (shearCol b ≤ y ∧ y ≤ shearCol a)) →
        (S.slot (S.bandOf a) y).IsGap)

lemma sameStackData_refl (a : Hex) : S.SameStackData a a := by
  cases h : S.slotAt a with
  | block j => exact Or.inl ⟨j, j, h, h, rfl, rfl⟩
  | gapL =>
    refine Or.inr ⟨by rw [h]; trivial, by rw [h]; trivial, rfl, fun y hy => ?_⟩
    rw [show y = shearCol a by omega, ← S.slotAt_eq a, h]
    trivial
  | gapR =>
    refine Or.inr ⟨by rw [h]; trivial, by rw [h]; trivial, rfl, fun y hy => ?_⟩
    rw [show y = shearCol a by omega, ← S.slotAt_eq a, h]
    trivial

lemma sameStackData_symm {a b : Hex} (h : S.SameStackData a b) : S.SameStackData b a := by
  rcases h with ⟨ja, jb, ha, hb, hband, hcol⟩ | ⟨ha, hb, hband, hy⟩
  · exact Or.inl ⟨jb, ja, hb, ha, hband.symm, hcol.symm⟩
  · refine Or.inr ⟨hb, ha, hband.symm, fun y h1 => ?_⟩
    rw [← hband]
    exact hy y (by omega)

lemma sameStackData_trans {a b c : Hex} (h : S.SameStackData a b) (h' : S.SameStackData b c) :
    S.SameStackData a c := by
  rcases h with ⟨ja, jb, ha, hb, hband, hcol⟩ | ⟨ha, hb, hband, hy⟩
  · rcases h' with ⟨jb', jc, hb', hc, hband', hcol'⟩ | ⟨hb', -, -, -⟩
    · rw [hb] at hb'
      injection hb' with e
      exact Or.inl ⟨ja, jc, ha, hc, hband.trans hband', by rw [hcol, e]; exact hcol'⟩
    · rw [hb] at hb'; exact hb'.elim
  · rcases h' with ⟨jb', jc, hb', hc, hband', hcol'⟩ | ⟨hb', hc, hband', hy'⟩
    · rw [hb'] at hb; exact hb.elim
    · refine Or.inr ⟨ha, hc, hband.trans hband', fun y h1 => ?_⟩
      rcases le_total y (shearCol b) with hle | hle
      · rcases h1 with ⟨p, -⟩ | ⟨p, -⟩
        · exact hy y (Or.inl ⟨p, hle⟩)
        · rw [hband]; exact hy' y (Or.inr ⟨p, hle⟩)
      · rcases h1 with ⟨-, q⟩ | ⟨-, q⟩
        · rw [hband]; exact hy' y (Or.inl ⟨hle, q⟩)
        · exact hy y (Or.inr ⟨hle, q⟩)

/-- Cells of one stick lie in the same stack. -/
lemma sameStackData_of_stickOf_eq {a b : Hex} (h : S.toTiling.stickOf a = S.toTiling.stickOf b) :
    S.SameStackData a b := by
  have hmem : a ∈ S.toTiling.stickOf b := by
    rw [← h]; exact S.toTiling.self_mem_stickOf a
  cases hb : S.slotAt b with
  | block jb =>
    rw [S.mem_stickOf_block_iff hb] at hmem
    obtain ⟨k, hk, hkc⟩ : ∃ k : ℕ, k ≤ n ∧ shearCol a = shearCol b - jb + k :=
      ⟨(shearCol a - (shearCol b - jb)).toNat, by omega, by omega⟩
    have hband : S.bandOf a = S.bandOf b := S.bandOf_congr hmem.1
    have hja : S.slotAt a = .block k := by
      rw [S.slotAt_eq a, hband, hkc]
      exact S.slotAt_of_block hb hk
    exact Or.inl ⟨k, jb, hja, hb, hband, by omega⟩
  | gapL =>
    have hgap : (S.slotAt b).IsGap := by rw [hb]; trivial
    rw [S.mem_stickOf_gap_iff hgap] at hmem
    have hsame : S.slotAt a = S.slotAt b := by rw [S.slotAt_eq a, S.slotAt_eq b, hmem.1, hmem.2]
    refine Or.inr ⟨by rw [hsame]; exact hgap, hgap, hmem.2, fun y h1 => ?_⟩
    rw [show y = shearCol a by omega, ← S.slotAt_eq a, hsame]
    exact hgap
  | gapR =>
    have hgap : (S.slotAt b).IsGap := by rw [hb]; trivial
    rw [S.mem_stickOf_gap_iff hgap] at hmem
    have hsame : S.slotAt a = S.slotAt b := by rw [S.slotAt_eq a, S.slotAt_eq b, hmem.1, hmem.2]
    refine Or.inr ⟨by rw [hsame]; exact hgap, hgap, hmem.2, fun y h1 => ?_⟩
    rw [show y = shearCol a by omega, ← S.slotAt_eq a, hsame]
    exact hgap

/-! ### Identifying the stacked pairs -/

/-- Every direction occurring in the tiling of a schematic is `W`, `SE` or `NW`. -/
lemma dirAt_eq_three (c : Hex) :
    S.dirAt c = HexDir.W ∨ S.dirAt c = HexDir.SE ∨ S.dirAt c = HexDir.NW := by
  rcases S.dirAt_cases c with ⟨-, -, hd⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
  exacts [Or.inl hd, Or.inr (Or.inl hd), Or.inr (Or.inr hd)]

/-- The leftmost column of the block of a block cell. -/
lemma slot_block_start {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.slot (S.bandOf c) (shearCol c - j) = .block 0 := by
  have := S.slotAt_of_block h (k := 0) (Nat.zero_le n)
  simpa using this

/-- A stacked pair of horizontal sticks lies inside one block. -/
lemma sameStackData_of_stackedBy_block {c c' : Hex} {j : ℕ} {e : HexDir}
    (hc : S.slotAt c = .block j) (h : S.toTiling.StackedBy c c' e) : S.SameStackData c c' := by
  obtain ⟨hax, hpar, hmem⟩ := h
  rw [toTiling_dir, S.dirAt_block hc] at hax hpar
  have hdc' : S.dirAt c' = HexDir.W := by
    rcases hpar with h1 | h1
    · rw [toTiling_dir] at h1; exact h1
    · exfalso
      rw [toTiling_dir] at h1
      rcases S.dirAt_eq_three c' with hd | hd | hd <;> rw [hd] at h1 <;> revert h1 <;> decide
  obtain ⟨j', hc'⟩ := S.exists_block_of_dirAt_W hdc'
  have hjn : j ≤ n := S.slotAt_block_le hc
  have hjn' : j' ≤ n := S.slotAt_block_le hc'
  have h4 := S.four_le
  have hA := hmem _ (S.left_mem_stickOf hc)
  have hB := hmem _ (S.right_mem_stickOf hc)
  rw [S.mem_stickOf_block_iff hc'] at hA hB
  have hbase := S.slot_block_start hc
  have hbase' := S.slot_block_start hc'
  have hbandc : S.bandOf c = bandRow n (shearRow c) := rfl
  have hbandc' : S.bandOf c' = bandRow n (shearRow c') := rfl
  have hsub0 := S.subOf_nonneg c
  have hsubn := S.subOf_le c
  have hsubdef : S.subOf c = subRow n (shearRow c) := rfl
  rcases HexDir.cases_six e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (Or.inr (by decide)) hax
  · -- `e = NE`
    exfalso
    simp only [shearRow_nbr_NE, shearCol_nbr_NE, shearRow_shearCell, shearCol_shearCell] at hA hB
    have hstart : shearCol c - j + 1 = shearCol c' - j' := by omega
    have hrow : shearRow c + 1 = shearRow c' := hA.1
    by_cases hs : S.subOf c < n
    · have hband : S.bandOf c' = S.bandOf c := by
        rw [hbandc', ← hrow, (bandRow_succ_of_lt (n := n) hs).1, ← hbandc]
      rw [hband, ← hstart] at hbase'
      have h1 : S.slot (S.bandOf c) (shearCol c - j + 1) = .block 1 :=
        S.step_of_block_lt hbase (by omega)
      rw [hbase'] at h1
      simp at h1
    · have hsn : S.subOf c = n := by omega
      have hband : S.bandOf c' = S.bandOf c + 1 := by
        rw [hbandc', ← hrow, bandRow_succ_of_eq_n (n := n) (by rw [← hsubdef, hsn]), ← hbandc]
      rw [hband, ← hstart] at hbase'
      exact S.no_block_zero_above_succ hbase hbase'
  · -- `e = NW`
    simp only [shearRow_nbr_NW, shearCol_nbr_NW, shearRow_shearCell, shearCol_shearCell] at hA hB
    have hstart : shearCol c - j = shearCol c' - j' := by omega
    have hrow : shearRow c + 1 = shearRow c' := hA.1
    by_cases hs : S.subOf c < n
    · have hband : S.bandOf c' = S.bandOf c := by
        rw [hbandc', ← hrow, (bandRow_succ_of_lt (n := n) hs).1, ← hbandc]
      exact Or.inl ⟨j, j', hc, hc', hband.symm, hstart⟩
    · exfalso
      have hsn : S.subOf c = n := by omega
      have hband : S.bandOf c' = S.bandOf c + 1 := by
        rw [hbandc', ← hrow, bandRow_succ_of_eq_n (n := n) (by rw [← hsubdef, hsn]), ← hbandc]
      rw [hband, ← hstart] at hbase'
      exact S.no_block_zero_above hbase hbase'
  · exact absurd (Or.inl rfl) hax
  · -- `e = SW`
    exfalso
    simp only [shearRow_nbr_SW, shearCol_nbr_SW, shearRow_shearCell, shearCol_shearCell] at hA hB
    have hstart : shearCol c - j - 1 = shearCol c' - j' := by omega
    have hrow : shearRow c - 1 = shearRow c' := hA.1
    by_cases hs : 0 < S.subOf c
    · have hband : S.bandOf c' = S.bandOf c := by
        rw [hbandc', ← hrow, (bandRow_pred_of_pos (n := n) hs).1, ← hbandc]
      rw [hband, ← hstart] at hbase'
      have h1 : S.slot (S.bandOf c) (shearCol c - j - 1) = .gapR := S.gapR_of_block hc
      rw [hbase'] at h1
      exact Slot.noConfusion h1
    · have hs0 : S.subOf c = 0 := by omega
      have hband : S.bandOf c' = S.bandOf c - 1 := by
        rw [hbandc', ← hrow, bandRow_pred_of_eq_zero (n := n) (by rw [← hsubdef, hs0]), ← hbandc]
      rw [hband, ← hstart] at hbase'
      exact S.no_block_zero_below_pred hbase hbase'
  · -- `e = SE`
    simp only [shearRow_nbr_SE, shearCol_nbr_SE, shearRow_shearCell, shearCol_shearCell] at hA hB
    have hstart : shearCol c - j = shearCol c' - j' := by omega
    have hrow : shearRow c - 1 = shearRow c' := hA.1
    by_cases hs : 0 < S.subOf c
    · have hband : S.bandOf c' = S.bandOf c := by
        rw [hbandc', ← hrow, (bandRow_pred_of_pos (n := n) hs).1, ← hbandc]
      exact Or.inl ⟨j, j', hc, hc', hband.symm, hstart⟩
    · exfalso
      have hs0 : S.subOf c = 0 := by omega
      have hband : S.bandOf c' = S.bandOf c - 1 := by
        rw [hbandc', ← hrow, bandRow_pred_of_eq_zero (n := n) (by rw [← hsubdef, hs0]), ← hbandc]
      rw [hband, ← hstart] at hbase'
      exact S.no_block_zero_below hbase hbase'

/-- A stacked pair of left-slanting sticks lies inside one gap. -/
lemma sameStackData_of_stackedBy_gap {c c' : Hex} {e : HexDir}
    (hc : (S.slotAt c).IsGap) (h : S.toTiling.StackedBy c c' e) : S.SameStackData c c' := by
  obtain ⟨hax, hpar, hmem⟩ := h
  have h4 := S.four_le
  have hdc : S.dirAt c = HexDir.SE ∨ S.dirAt c = HexDir.NW := by
    rcases S.dirAt_cases c with ⟨j, hj, -⟩ | ⟨-, hd⟩ | ⟨-, hd⟩
    · rw [hj] at hc; exact hc.elim
    · exact Or.inl hd
    · exact Or.inr hd
  have hc' : (S.slotAt c').IsGap := by
    refine S.isGap_of_dirAt_ne_W ?_
    intro hw
    rw [toTiling_dir, toTiling_dir, hw] at hpar
    rcases hdc with hd | hd <;> rw [hd] at hpar <;> revert hpar <;> decide
  rw [toTiling_dir] at hax
  have hbot := hmem _ (S.bot_mem_stickOf hc)
  have htop := hmem _ (S.top_mem_stickOf hc)
  rw [S.mem_stickOf_gap_iff hc'] at hbot htop
  have hbc : S.bandOf c = bandRow n (shearRow c) := rfl
  have hbc' : S.bandOf c' = bandRow n (shearRow c') := rfl
  simp only [bandOf] at hbot htop
  have hself : bandRow n (((n : ℤ) + 1) * bandRow n (shearRow c)) = bandRow n (shearRow c) := by
    rw [show ((n : ℤ) + 1) * bandRow n (shearRow c)
        = ((n : ℤ) + 1) * bandRow n (shearRow c) + 0 from by ring]
    exact bandRow_eq n _ _ le_rfl (by positivity)
  have htopband :
      bandRow n (((n : ℤ) + 1) * bandRow n (shearRow c) + n) = bandRow n (shearRow c) :=
    bandRow_eq n _ _ (by positivity) le_rfl
  rcases HexDir.cases_six e with rfl | rfl | rfl | rfl | rfl | rfl
  · -- `e = E`
    simp only [shearCol_nbr_E, shearRow_nbr_E, shearCol_shearCell, shearRow_shearCell] at hbot htop
    have hband : S.bandOf c' = S.bandOf c := by rw [hbc', ← hbot.2, hself, hbc]
    have hcol : shearCol c' = shearCol c + 1 := hbot.1.symm
    refine Or.inr ⟨hc, hc', hband.symm, fun y hy => ?_⟩
    have hy2 : y = shearCol c ∨ y = shearCol c' := by omega
    rcases hy2 with rfl | rfl
    · exact hc
    · rw [← hband]; exact hc'
  · -- `e = NE`
    exfalso
    simp only [shearCol_nbr_NE, shearRow_nbr_NE, shearCol_shearCell,
      shearRow_shearCell] at hbot htop
    have e1 : bandRow n (((n : ℤ) + 1) * bandRow n (shearRow c) + 1) = bandRow n (shearRow c) :=
      bandRow_eq n _ _ (by omega) (by omega)
    have e2 : bandRow n (((n : ℤ) + 1) * bandRow n (shearRow c) + n + 1)
        = bandRow n (shearRow c) + 1 := by
      rw [show ((n : ℤ) + 1) * bandRow n (shearRow c) + (n : ℤ) + 1
          = ((n : ℤ) + 1) * (bandRow n (shearRow c) + 1) + 0 from by ring]
      exact bandRow_eq n _ _ le_rfl (by positivity)
    rw [e1] at hbot
    rw [e2] at htop
    omega
  · exact absurd (by rcases hdc with hd | hd <;> rw [hd] <;> decide) hax
  · -- `e = W`
    simp only [shearCol_nbr_W, shearRow_nbr_W, shearCol_shearCell, shearRow_shearCell] at hbot htop
    have hband : S.bandOf c' = S.bandOf c := by rw [hbc', ← hbot.2, hself, hbc]
    have hcol : shearCol c' = shearCol c - 1 := hbot.1.symm
    refine Or.inr ⟨hc, hc', hband.symm, fun y hy => ?_⟩
    have hy2 : y = shearCol c ∨ y = shearCol c' := by omega
    rcases hy2 with rfl | rfl
    · exact hc
    · rw [← hband]; exact hc'
  · -- `e = SW`
    exfalso
    simp only [shearCol_nbr_SW, shearRow_nbr_SW, shearCol_shearCell,
      shearRow_shearCell] at hbot htop
    have e1 : bandRow n (((n : ℤ) + 1) * bandRow n (shearRow c) - 1)
        = bandRow n (shearRow c) - 1 := by
      rw [show ((n : ℤ) + 1) * bandRow n (shearRow c) - 1
          = ((n : ℤ) + 1) * (bandRow n (shearRow c) - 1) + n from by ring]
      exact bandRow_eq n _ _ (by positivity) le_rfl
    have e2 : bandRow n (((n : ℤ) + 1) * bandRow n (shearRow c) + n - 1)
        = bandRow n (shearRow c) := by
      rw [show ((n : ℤ) + 1) * bandRow n (shearRow c) + (n : ℤ) - 1
          = ((n : ℤ) + 1) * bandRow n (shearRow c) + ((n : ℤ) - 1) from by ring]
      exact bandRow_eq n _ _ (by omega) (by omega)
    rw [e1] at hbot
    rw [e2] at htop
    omega
  · exact absurd (by rcases hdc with hd | hd <;> rw [hd] <;> decide) hax
/-- Every stacked pair of the tiling of a schematic lies inside one block or one gap. -/
theorem sameStackData_of_stackedBy {c c' : Hex} {e : HexDir}
    (h : S.toTiling.StackedBy c c' e) : S.SameStackData c c' := by
  cases hc : S.slotAt c with
  | block j => exact S.sameStackData_of_stackedBy_block hc h
  | gapL => exact S.sameStackData_of_stackedBy_gap (by rw [hc]; trivial) h
  | gapR => exact S.sameStackData_of_stackedBy_gap (by rw [hc]; trivial) h

/-! ### Building chains inside a block or a gap -/

lemma sameStack_of_stickOf_eq {a b : Hex} (h : S.toTiling.stickOf a = S.toTiling.stickOf b) :
    S.toTiling.SameStack a b :=
  Relation.ReflTransGen.single (Or.inl h)

lemma sameStack_of_stackedBy {a b : Hex} {e : HexDir} (h : S.toTiling.StackedBy a b e) :
    S.toTiling.SameStack a b :=
  Relation.ReflTransGen.single (Or.inr ⟨e, h⟩)

/-- Every cell of a block lies in the same stack as the bottom-left cell of the block. -/
lemma sameStack_block_base (k : ℕ) : ∀ (c : Hex) (j : ℕ), (S.subOf c).toNat = k →
    S.slotAt c = .block j →
    S.toTiling.SameStack c (shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c)) := by
  induction k with
  | zero =>
    intro c j hk hc
    have h0 : S.subOf c = 0 := by have := S.subOf_nonneg c; omega
    have hrow : shearRow c = ((n : ℤ) + 1) * S.bandOf c := by
      have := bandRow_mul_add n (shearRow c)
      simp only [bandOf, subOf] at *
      omega
    refine S.sameStack_of_stickOf_eq ?_
    rw [← hrow]
    exact (S.toTiling.stickOf_eq_of_mem (S.left_mem_stickOf hc)).symm
  | succ k ih =>
    intro c j hk hc
    have h0 : 0 < S.subOf c := by have := S.subOf_nonneg c; omega
    have hd : S.slotAt (nbr c HexDir.SE) = .block j := by rw [S.slotAt_nbr_SE h0, hc]
    have hsub : S.subOf (nbr c HexDir.SE) = S.subOf c - 1 := S.subOf_nbr_SE h0
    have ih' := ih (nbr c HexDir.SE) j (by omega) hd
    rw [show shearCol (nbr c HexDir.SE) = shearCol c from by simp] at ih'
    rw [show S.bandOf (nbr c HexDir.SE) = S.bandOf c from
      by rw [bandOf, shearRow_nbr_SE, (bandRow_pred_of_pos (n := n) h0).1, bandOf]] at ih'
    exact StickTiling.SameStack.trans _ (S.sameStack_of_stackedBy (S.stackedBy_SE hc h0)) ih'

/-- Walking right inside a gap stays in the same stack. -/
lemma sameStack_gap_right (k : ℕ) : ∀ c : Hex, (S.slotAt c).IsGap →
    (∀ y : ℤ, shearCol c ≤ y → y ≤ shearCol c + k → (S.slot (S.bandOf c) y).IsGap) →
    S.toTiling.SameStack c (shearCell (shearCol c + k) (shearRow c)) := by
  induction k with
  | zero =>
    intro c _ _
    rw [show ((0 : ℕ) : ℤ) = 0 from rfl, add_zero, shearCell_shear]
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro c hc hy
    have hcold : shearCol (nbr c HexDir.E) = shearCol c + 1 := by simp
    have hrowd : shearRow (nbr c HexDir.E) = shearRow c := by simp
    have hbandd : S.bandOf (nbr c HexDir.E) = S.bandOf c := S.bandOf_congr hrowd
    have hdg : (S.slotAt (nbr c HexDir.E)).IsGap := by
      rw [S.slotAt_nbr_E]
      exact hy _ (by omega) (by push_cast; omega)
    have ih' := ih (nbr c HexDir.E) hdg (by
      intro y h1 h2
      rw [hbandd]
      rw [hcold] at h1 h2
      exact hy y (by omega) (by push_cast at h2 ⊢; omega))
    rw [hcold, hrowd] at ih'
    refine StickTiling.SameStack.trans _ (S.sameStack_of_stackedBy (S.stackedBy_E hc hdg)) ?_
    rw [show shearCol c + 1 + (k : ℤ) = shearCol c + ((k + 1 : ℕ) : ℤ) from by push_cast; ring] at ih'
    exact ih'

lemma sameStack_of_sameStackData_gap_le {a b : Hex} (ha : (S.slotAt a).IsGap)
    (hb : (S.slotAt b).IsGap) (hband : S.bandOf a = S.bandOf b) (hle : shearCol a ≤ shearCol b)
    (hy : ∀ y : ℤ, shearCol a ≤ y → y ≤ shearCol b → (S.slot (S.bandOf a) y).IsGap) :
    S.toTiling.SameStack a b := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, shearCol a + k = shearCol b :=
    ⟨(shearCol b - shearCol a).toNat, by omega⟩
  have h1 := S.sameStack_gap_right k a ha (by intro y h1 h2; exact hy y h1 (by omega))
  refine StickTiling.SameStack.trans _ h1 (S.sameStack_of_stickOf_eq ?_)
  refine S.toTiling.stickOf_eq_of_mem ?_
  rw [S.mem_stickOf_gap_iff hb]
  refine ⟨by rw [shearCol_shearCell, hk], ?_⟩
  rw [bandOf_shearCell, ← hband, bandOf]

/-- Two cells of the tiling of a schematic lie in the same stack exactly when they are cells of
one block or cells of one gap. -/
theorem sameStack_iff (a b : Hex) : S.toTiling.SameStack a b ↔ S.SameStackData a b := by
  constructor
  · intro h
    induction h with
    | refl => exact S.sameStackData_refl a
    | @tail y x hay hyx ih =>
      refine S.sameStackData_trans ih ?_
      rcases hyx with hstick | ⟨e, hpair⟩
      · exact S.sameStackData_of_stickOf_eq hstick
      · exact S.sameStackData_of_stackedBy hpair
  · intro h
    rcases h with ⟨ja, jb, ha, hb, hband, hcol⟩ | ⟨ha, hb, hband, hyy⟩
    · have h1 := S.sameStack_block_base (S.subOf a).toNat a ja rfl ha
      have h2 := S.sameStack_block_base (S.subOf b).toNat b jb rfl hb
      rw [hcol, hband] at h1
      exact StickTiling.SameStack.trans _ h1 (StickTiling.SameStack.symm _ h2)
    · rcases le_total (shearCol a) (shearCol b) with hle | hle
      · exact S.sameStack_of_sameStackData_gap_le ha hb hband hle
          (fun y h1 h2 => hyy y (Or.inl ⟨h1, h2⟩))
      · refine StickTiling.SameStack.symm _ (S.sameStack_of_sameStackData_gap_le hb ha hband.symm hle ?_)
        intro y h1 h2
        rw [← hband]
        exact hyy y (Or.inr ⟨h1, h2⟩)

end Schematic

end StickPolyhex
