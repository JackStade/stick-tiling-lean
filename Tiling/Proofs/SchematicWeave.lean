import Tiling.Proofs.SchematicAbove

/-!
# Schematics describe weave patterns

This file proves the main result about the block schematics of Section 2.3 of the paper
(Figure 21): the tiling `Schematic.toTiling` described by a schematic with blocks of length `n`
forms a weave pattern, for the orientation `HexDir.W`.

The nine conditions of `StickTiling.IsWeavePattern` are checked one by one; the heart of the
matter is the description of the stacks of `Schematic.toTiling` obtained in
`Tiling/Proofs/SchematicStacks.lean` and `Tiling/Proofs/SchematicStackSets.lean`: the
horizontal stacks are exactly the blocks of the schematic and the vertical stacks are exactly
its gaps.
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-! ### Two horizontal stacks above and two below -/

/-- Exactly two horizontal stacks lie above a given one: the two blocks of the next row of the
schematic that overlap the given block. -/
lemma two_above {c : Hex} {j : ℕ} (hc : S.slotAt c = .block j) :
    ∃ a₁ a₂, S.toTiling.dir a₁ = HexDir.W ∧ S.toTiling.dir a₂ = HexDir.W ∧
      ¬ S.toTiling.SameStack a₁ a₂ ∧ S.toTiling.StackAbove HexDir.W c a₁ ∧
      S.toTiling.StackAbove HexDir.W c a₂ ∧
      ∀ a, S.toTiling.dir a = HexDir.W → S.toTiling.StackAbove HexDir.W c a →
        S.toTiling.SameStack a a₁ ∨ S.toTiling.SameStack a a₂ := by
  have h4 := S.four_le
  have hstart : S.slot (S.bandOf c) (shearCol c - j) = .block 0 := S.slot_block_start hc
  have hgL : S.slot (S.bandOf c) (shearCol c - j + n + 1) = .gapL := S.slot_gapL_of_block hc
  obtain ⟨j1, hj1⟩ := S.exists_block_of_not_isGap
    (S.not_isGap_above_of_block hstart (Or.inl (by omega)))
  obtain ⟨j2, hj2⟩ := S.exists_block_of_not_isGap
    (S.not_isGap_above_of_isGap (show (S.slot (S.bandOf c) (shearCol c - j + n + 1)).IsGap by
      rw [hgL]; trivial))
  have hj1n := S.block_le hj1
  have hj2n := S.block_le hj2
  have hs1 : S.slot (S.bandOf c + 1) (shearCol c - j - j1) = .block 0 := S.slot_block_zero hj1
  have hs2 : S.slot (S.bandOf c + 1) (shearCol c - j + n + 1 - j2) = .block 0 :=
    S.slot_block_zero hj2
  have ha1 : S.slotAt (S.gcell (shearCol c - j) (S.bandOf c + 1) 0) = .block j1 := by
    rw [S.slotAt_gcell le_rfl (by positivity)]; exact hj1
  have hb1 : S.bandOf (S.gcell (shearCol c - j) (S.bandOf c + 1) 0) = S.bandOf c + 1 :=
    S.bandOf_gcell le_rfl (by positivity) _ _
  have ha2 : S.slotAt (S.gcell (shearCol c - j + n + 1) (S.bandOf c + 1) 0) = .block j2 := by
    rw [S.slotAt_gcell le_rfl (by positivity)]; exact hj2
  have hb2 : S.bandOf (S.gcell (shearCol c - j + n + 1) (S.bandOf c + 1) 0) = S.bandOf c + 1 :=
    S.bandOf_gcell le_rfl (by positivity) _ _
  refine ⟨S.gcell (shearCol c - j) (S.bandOf c + 1) 0,
    S.gcell (shearCol c - j + n + 1) (S.bandOf c + 1) 0, S.dirAt_block ha1, S.dirAt_block ha2,
    ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [S.sameStack_block_iff ha1 ha2, S.shearCol_gcell, S.shearCol_gcell]
    rintro ⟨-, hcc⟩
    omega
  · rw [S.sameStack_block_iff hc ha1, hb1]
    rintro ⟨hbb, -⟩
    omega
  · refine ⟨S.gcell (shearCol c - j) (S.bandOf c) n,
      S.sameStack_gcell_block hc (by positivity) le_rfl hstart le_rfl (by omega) rfl rfl, Or.inr ?_⟩
    rw [show (HexDir.W + 5 : HexDir) = HexDir.NW from by decide, S.gcell_nbr_NW_top]
    exact Relation.ReflTransGen.refl
  · rw [S.sameStack_block_iff hc ha2, hb2]
    rintro ⟨hbb, -⟩
    omega
  · refine ⟨S.gcell (shearCol c - j + n) (S.bandOf c) n,
      S.sameStack_gcell_block hc (by positivity) le_rfl hstart (by omega) le_rfl rfl rfl,
      Or.inl ?_⟩
    rw [show (HexDir.W + 4 : HexDir) = HexDir.NE from by decide, S.gcell_nbr_NE_top]
    exact Relation.ReflTransGen.refl
  · intro a had hab
    obtain ⟨ja, ha⟩ := S.exists_block_of_dirAt_W had
    obtain ⟨col, hcol1, hcol2, hbanda, hsa1, hsa2⟩ := S.stackAbove_col hc ha hab
    have hsa : S.slot (S.bandOf c + 1) (shearCol a - ja) = .block 0 := by
      have h := S.slot_block_start ha; rwa [hbanda] at h
    rcases S.blockStart_eq_or hs1 hs2 hsa (by omega) (by omega) hsa1 hsa2 (by omega) with h | h
    · exact Or.inl ((S.sameStack_block_iff ha ha1).2
        ⟨by rw [hbanda, hb1], by rw [S.shearCol_gcell]; omega⟩)
    · exact Or.inr ((S.sameStack_block_iff ha ha2).2
        ⟨by rw [hbanda, hb2], by rw [S.shearCol_gcell]; omega⟩)

/-- Exactly two horizontal stacks lie below a given one. -/
lemma two_below {c : Hex} {j : ℕ} (hc : S.slotAt c = .block j) :
    ∃ b₁ b₂, S.toTiling.dir b₁ = HexDir.W ∧ S.toTiling.dir b₂ = HexDir.W ∧
      ¬ S.toTiling.SameStack b₁ b₂ ∧ S.toTiling.StackBelow HexDir.W c b₁ ∧
      S.toTiling.StackBelow HexDir.W c b₂ ∧
      ∀ b, S.toTiling.dir b = HexDir.W → S.toTiling.StackBelow HexDir.W c b →
        S.toTiling.SameStack b b₁ ∨ S.toTiling.SameStack b b₂ := by
  have h4 := S.four_le
  have hstart : S.slot (S.bandOf c) (shearCol c - j) = .block 0 := S.slot_block_start hc
  have hgL : S.slot (S.bandOf c) (shearCol c - j + n + 1) = .gapL := S.slot_gapL_of_block hc
  have hgR : S.slot (S.bandOf c) (shearCol c - j - 1) = .gapR := S.slot_gapR_of_block hc
  obtain ⟨j1, hj12, hj1n, hj1⟩ := S.slot_overlap (S.bandOf c - 1) (shearCol c - j - 1) (by
    rw [show S.bandOf c - 1 + 1 = S.bandOf c from by ring, hgR]; trivial)
  obtain ⟨j2, hj22, hj2n, hj2⟩ := S.slot_overlap (S.bandOf c - 1) (shearCol c - j + n + 1) (by
    rw [show S.bandOf c - 1 + 1 = S.bandOf c from by ring, hgL]; trivial)
  have hs1 : S.slot (S.bandOf c - 1) (shearCol c - j - 1 - j1) = .block 0 := S.slot_block_zero hj1
  have hs2 : S.slot (S.bandOf c - 1) (shearCol c - j + n + 1 - j2) = .block 0 :=
    S.slot_block_zero hj2
  have hb1 : S.bandOf (S.gcell (shearCol c - j - 1) (S.bandOf c - 1) n) = S.bandOf c - 1 :=
    S.bandOf_gcell (by positivity) le_rfl _ _
  have hb2 : S.bandOf (S.gcell (shearCol c - j + n) (S.bandOf c - 1) n) = S.bandOf c - 1 :=
    S.bandOf_gcell (by positivity) le_rfl _ _
  have ha1 : S.slotAt (S.gcell (shearCol c - j - 1) (S.bandOf c - 1) n)
      = .block ((shearCol c - j - 1 - (shearCol c - j - 1 - j1)).toNat) :=
    S.slotAt_gcell_block (by positivity) le_rfl hs1 (by omega) (by omega)
  have ha2 : S.slotAt (S.gcell (shearCol c - j + n) (S.bandOf c - 1) n)
      = .block ((shearCol c - j + n - (shearCol c - j + n + 1 - j2)).toNat) :=
    S.slotAt_gcell_block (by positivity) le_rfl hs2 (by omega) (by omega)
  refine ⟨S.gcell (shearCol c - j - 1) (S.bandOf c - 1) n,
    S.gcell (shearCol c - j + n) (S.bandOf c - 1) n, S.dirAt_block ha1, S.dirAt_block ha2,
    ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [S.sameStack_block_iff ha1 ha2, S.shearCol_gcell, S.shearCol_gcell]
    rintro ⟨-, hcc⟩
    omega
  · rw [S.sameStack_block_iff hc ha1, hb1]
    rintro ⟨hbb, -⟩
    omega
  · refine ⟨S.gcell (shearCol c - j) (S.bandOf c) 0,
      S.sameStack_gcell_block hc le_rfl (by positivity) hstart le_rfl (by omega) rfl rfl,
      Or.inl ?_⟩
    rw [show (HexDir.W + 1 : HexDir) = HexDir.SW from by decide, S.gcell_nbr_SW_bot]
    exact Relation.ReflTransGen.refl
  · rw [S.sameStack_block_iff hc ha2, hb2]
    rintro ⟨hbb, -⟩
    omega
  · refine ⟨S.gcell (shearCol c - j + n) (S.bandOf c) 0,
      S.sameStack_gcell_block hc le_rfl (by positivity) hstart (by omega) le_rfl rfl rfl,
      Or.inr ?_⟩
    rw [show (HexDir.W + 2 : HexDir) = HexDir.SE from by decide, S.gcell_nbr_SE_bot]
    exact Relation.ReflTransGen.refl
  · intro b hbd hbb
    obtain ⟨jb, hb⟩ := S.exists_block_of_dirAt_W hbd
    obtain ⟨col, hcol1, hcol2, hbandb, hsb1, hsb2⟩ := S.stackBelow_col hc hb hbb
    have hsb : S.slot (S.bandOf c - 1) (shearCol b - jb) = .block 0 := by
      have h := S.slot_block_start hb; rwa [hbandb] at h
    rcases S.blockStart_eq_or hs1 hs2 hsb (by omega) (by omega) hsb1 hsb2 (by omega) with h | h
    · exact Or.inl ((S.sameStack_block_iff hb ha1).2
        ⟨by rw [hbandb, hb1], by rw [S.shearCol_gcell]; omega⟩)
    · exact Or.inr ((S.sameStack_block_iff hb ha2).2
        ⟨by rw [hbandb, hb2], by rw [S.shearCol_gcell]; omega⟩)

/-! ### Adjacent horizontal stacks overlap -/

/-- Two adjacent horizontal stacks overlap by at least one concave corner. -/
lemma overlap_of {c c' : Hex} {j jc' : ℕ} (hc : S.slotAt c = .block j)
    (hc' : S.slotAt c' = .block jc') (hab : S.toTiling.StackAbove HexDir.W c c') :
    ∃ x, S.toTiling.SameStack c x ∧ S.toTiling.idx x < n + 1 ∧
      S.toTiling.SameStack c' (nbr x (HexDir.W + 5)) := by
  have h4 := S.four_le
  obtain ⟨col, hcol1, hcol2, hband, hsa1, hsa2⟩ := S.stackAbove_col hc hc' hab
  have hstart : S.slot (S.bandOf c) (shearCol c - j) = .block 0 := S.slot_block_start hc
  have hstart' : S.slot (S.bandOf c + 1) (shearCol c' - jc') = .block 0 := by
    have h := S.slot_block_start hc'; rwa [hband] at h
  have hA : shearCol c - j + 1 ≤ shearCol c' - jc' + n := by
    by_contra hcon
    have hgL : S.slot (S.bandOf c + 1) (shearCol c' - jc' + n + 1) = .gapL := by
      have h := S.gapL_of_block_n (r := S.bandOf c + 1) (x := shearCol c' - jc') (j := 0) hstart'
      simpa using h
    refine S.not_isGap_above_of_block
      (S.slot_of_start hstart (show shearCol c - j ≤ shearCol c - j + 1 from by omega)
        (by omega)) (Or.inl (by omega)) ?_
    rw [show shearCol c - j + 1 = shearCol c' - jc' + n + 1 from by omega, hgL]
    trivial
  have hB : shearCol c' - jc' ≤ shearCol c - j + n := by
    by_contra hcon
    have hgR : S.slot (S.bandOf c + 1) (shearCol c' - jc' - 1) = .gapR :=
      S.gapR_of_block_zero hstart'
    refine S.not_isGap_above_of_block
      (S.slot_of_start hstart (by omega) (show shearCol c - j + n ≤ shearCol c - j + n from le_rfl))
      (Or.inr (by omega)) ?_
    rw [show shearCol c - j + n = shearCol c' - jc' - 1 from by omega, hgR]
    trivial
  obtain ⟨y, hy1, hy2, hy3, hy4⟩ : ∃ y : ℤ, shearCol c - j + 1 ≤ y ∧ y ≤ shearCol c - j + n ∧
      shearCol c' - jc' ≤ y ∧ y ≤ shearCol c' - jc' + n := by
    rcases le_total (shearCol c' - jc') (shearCol c - j + 1) with h | h
    · exact ⟨shearCol c - j + 1, le_rfl, by omega, h, by omega⟩
    · exact ⟨shearCol c' - jc', h, by omega, le_rfl, by omega⟩
  have hx : S.slotAt (S.gcell y (S.bandOf c) n) = .block ((y - (shearCol c - j)).toNat) :=
    S.slotAt_gcell_block (by positivity) le_rfl hstart (by omega) hy2
  refine ⟨S.gcell y (S.bandOf c) n, ?_, ?_, ?_⟩
  · exact S.sameStack_gcell_block hc (by positivity) le_rfl hstart (by omega) hy2 rfl rfl
  · rw [toTiling_idx, S.idxAt_block hx]
    omega
  · rw [show (HexDir.W + 5 : HexDir) = HexDir.NW from by decide, S.gcell_nbr_NW_top]
    exact S.sameStack_gcell_block hc' le_rfl (by positivity) hstart' hy3 hy4 hband rfl

/-! ### The four horizontal stacks of a cell of the grid enclose a vertical stack -/

/-- The grid-cell condition, for two stacks above `c` listed from left to right. -/
lemma grid_cell_ordered {c a₁ a₂ : Hex} {j j1 j2 : ℕ} {r x0 t1 t2 : ℤ}
    (hc : S.slotAt c = .block j) (hr : S.bandOf c = r) (hx0 : shearCol c - j = x0)
    (ha1 : S.slotAt a₁ = .block j1) (hb1 : S.bandOf a₁ = r + 1) (ht1 : shearCol a₁ - j1 = t1)
    (ha2 : S.slotAt a₂ = .block j2) (hb2 : S.bandOf a₂ = r + 1) (ht2 : shearCol a₂ - j2 = t2)
    (hlow : x0 - n ≤ t1) (hhigh : t2 ≤ x0 + n + 1) (hlt : t1 < t2) :
    ∃ a₃ v, S.toTiling.dir a₃ = HexDir.W ∧ S.toTiling.StackAbove HexDir.W a₁ a₃ ∧
      S.toTiling.StackAbove HexDir.W a₂ a₃ ∧ S.toTiling.SlantsLeft HexDir.W v ∧
      2 ≤ S.toTiling.stackHeight v ∧ S.toTiling.StackAdjacent v c ∧
      S.toTiling.StackAdjacent v a₁ ∧ S.toTiling.StackAdjacent v a₂ ∧
      S.toTiling.StackAdjacent v a₃ := by
  have h4 := S.four_le
  have hstart : S.slot r x0 = .block 0 := by rw [← hr, ← hx0]; exact S.slot_block_start hc
  have hs1 : S.slot (r + 1) t1 = .block 0 := by rw [← hb1, ← ht1]; exact S.slot_block_start ha1
  have hs2 : S.slot (r + 1) t2 = .block 0 := by rw [← hb2, ← ht2]; exact S.slot_block_start ha2
  have hgapL : S.slot (r + 1) (t1 + n + 1) = .gapL := by
    have h := S.gapL_of_block_n (r := r + 1) (x := t1) (j := 0) hs1
    simpa using h
  have hgapR : S.slot (r + 1) (t2 - 1) = .gapR := S.gapR_of_block_zero hs2
  have hfar : t1 + n + 2 ≤ t2 := by
    by_contra hcon
    by_cases hcase : t2 ≤ t1 + n
    · exact absurd (S.start_unique (y := t2) hs1 hs2 (by omega) hcase le_rfl (by omega)) (by omega)
    · have ht2eq : t2 = t1 + n + 1 := by omega
      rw [ht2eq, hgapL] at hs2
      exact Slot.noConfusion hs2
  have hne12 : t1 + n + 1 ≠ t2 - 1 := by
    intro h
    rw [h, hgapR] at hgapL
    exact Slot.noConfusion hgapL
  have hg12 : t1 + n + 1 < t2 - 1 := by omega
  have hallgap : ∀ z : ℤ, t1 + n + 1 ≤ z → z ≤ t2 - 1 → (S.slot (r + 1) z).IsGap := by
    intro z hz1 hz2
    exact S.isGap_between (by rw [hgapL]; trivial) (by rw [hgapR]; trivial) hz1 hz2 (by omega)
  -- the gap between the two blocks lies strictly inside the block of `c`
  have hin1 : x0 + 2 ≤ t1 + n + 1 := by
    obtain ⟨jj, hjj2, hjjn, hjj⟩ := S.slot_overlap r (t1 + n + 1)
      (by rw [hgapL]; trivial)
    have hb := S.slot_of_start hstart (show x0 ≤ t1 + n + 1 from by omega)
      (show t1 + n + 1 ≤ x0 + n from by omega)
    rw [hjj] at hb
    injection hb with e
    omega
  have hin2 : t2 - 1 ≤ x0 + n - 1 := by
    obtain ⟨jj, hjj2, hjjn, hjj⟩ := S.slot_overlap r (t2 - 1) (by rw [hgapR]; trivial)
    have hb := S.slot_of_start hstart (show x0 ≤ t2 - 1 from by omega)
      (show t2 - 1 ≤ x0 + n from by omega)
    rw [hjj] at hb
    injection hb with e
    omega
  -- the columns just outside the gap, in the row above, are block columns
  have hleftblock : S.slot (r + 1) (t1 + n) = .block ((t1 + n - t1).toNat) :=
    S.slot_of_start hs1 (by omega) (by omega)
  have hnogap : ∀ i : ℕ, i ≤ (t2 - 1 - (t1 + n + 1) + 2).toNat →
      ¬ (S.slot (r + 1 + 1) (t1 + n + i)).IsGap := by
    intro i hi
    have hi' : (i : ℤ) ≤ t2 - 1 - (t1 + n + 1) + 2 := by omega
    rcases eq_or_lt_of_le (show (0 : ℤ) ≤ (i : ℤ) from by positivity) with h0 | h0
    · rw [show t1 + (n : ℤ) + (i : ℤ) = t1 + n from by omega]
      exact S.not_isGap_above_of_block hleftblock (Or.inr (by omega))
    · rcases eq_or_lt_of_le hi' with hk | hk
      · rw [show t1 + (n : ℤ) + (i : ℤ) = t2 from by omega]
        exact S.not_isGap_above_of_block hs2 (Or.inl (by omega))
      · exact S.not_isGap_above_of_isGap (hallgap _ (by omega) (by omega))
  have hy0 : ¬ (S.slot (r + 1 + 1) (t1 + n)).IsGap := by
    have h := hnogap 0 (by omega)
    rwa [show t1 + (n : ℤ) + ((0 : ℕ) : ℤ) = t1 + n from by omega] at h
  obtain ⟨jy, hjy⟩ := S.exists_block_of_not_isGap hy0
  have hjyn := S.block_le hjy
  obtain ⟨jk, hjk, hstk⟩ := S.start_eq_of_no_gap hjy (t2 - 1 - (t1 + n + 1) + 2).toNat hnogap
  have hjkn := S.block_le hjk
  obtain ⟨jm, hjm, hstm⟩ := S.start_eq_of_no_gap hjy 1 (fun i hi => hnogap i (by omega))
  have hjmn := S.block_le hjm
  have hs3 : S.slot (r + 1 + 1) (t1 + n - jy) = .block 0 := S.slot_block_zero hjy
  -- the block `a₃`
  have ha3 : S.slotAt (S.gcell (t1 + n) (r + 1 + 1) 0) = .block jy := by
    rw [S.slotAt_gcell le_rfl (by positivity)]; exact hjy
  have hb3 : S.bandOf (S.gcell (t1 + n) (r + 1 + 1) 0) = r + 1 + 1 :=
    S.bandOf_gcell le_rfl (by positivity) _ _
  -- the gap `v`
  have hv : S.slotAt (S.gcell (t1 + n + 1) (r + 1) 0) = .gapL := by
    rw [S.slotAt_gcell le_rfl (by positivity)]; exact hgapL
  have hvgap : (S.slotAt (S.gcell (t1 + n + 1) (r + 1) 0)).IsGap := by rw [hv]; trivial
  have hbv : S.bandOf (S.gcell (t1 + n + 1) (r + 1) 0) = r + 1 :=
    S.bandOf_gcell le_rfl (by positivity) _ _
  have hnotv : ∀ (b : Hex) (jb : ℕ), S.slotAt b = .block jb →
      ¬ S.toTiling.SameStack (S.gcell (t1 + n + 1) (r + 1) 0) b := by
    intro b jb hb h
    exact S.not_sameStack_block_gap hb hvgap (StickTiling.SameStack.symm _ h)
  refine ⟨S.gcell (t1 + n) (r + 1 + 1) 0, S.gcell (t1 + n + 1) (r + 1) 0,
    S.dirAt_block ha3, ⟨?_, ?_⟩, ⟨?_, ?_⟩, Or.inl ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  -- `a₃` lies above `a₁`
  · rw [S.sameStack_block_iff ha1 ha3, hb1, hb3]
    rintro ⟨hbb, -⟩
    omega
  · refine ⟨S.gcell (t1 + n) (r + 1) n,
      S.sameStack_gcell_block ha1 (by positivity) le_rfl hs1 (by omega) (by omega) hb1 ht1,
      Or.inr ?_⟩
    rw [show (HexDir.W + 5 : HexDir) = HexDir.NW from by decide, S.gcell_nbr_NW_top]
    exact Relation.ReflTransGen.refl
  -- `a₃` lies above `a₂`
  · rw [S.sameStack_block_iff ha2 ha3, hb2, hb3]
    rintro ⟨hbb, -⟩
    omega
  · refine ⟨S.gcell t2 (r + 1) n,
      S.sameStack_gcell_block ha2 (by positivity) le_rfl hs2 le_rfl (by omega) hb2 ht2,
      Or.inr ?_⟩
    rw [show (HexDir.W + 5 : HexDir) = HexDir.NW from by decide, S.gcell_nbr_NW_top]
    exact S.sameStack_gcell_block ha3 le_rfl (by positivity) hs3 (by omega) (by omega) hb3
      (by rw [S.shearCol_gcell])
  -- `v` slants left
  · rw [toTiling_dir, S.dirAt_gapL hv]; decide
  -- the height of `v`
  · have hh := S.stackHeight_gap hvgap (g2 := t2 - 1) (by rw [S.shearCol_gcell]; omega)
      (by
        intro y hy1 hy2
        rw [hbv]
        rw [S.shearCol_gcell] at hy1
        exact hallgap y hy1 hy2)
      (by
        rw [hbv, S.shearCol_gcell,
          show t1 + (n : ℤ) + 1 - 1 = t1 + n from by ring, hleftblock]
        exact id)
      (by
        rw [hbv, show t2 - 1 + 1 = t2 from by ring, hs2]
        exact id)
    rw [hh, S.shearCol_gcell]
    omega
  -- `v` is adjacent to `c`
  · exact hnotv c j hc
  · refine ⟨S.gcell (t1 + n + 1) (r + 1) 0, HexDir.SE, Relation.ReflTransGen.refl, ?_⟩
    rw [S.gcell_nbr_SE_bot, show r + 1 - 1 = r from by ring]
    exact S.sameStack_gcell_block hc (by positivity) le_rfl hstart (by omega) (by omega) hr hx0
  -- `v` is adjacent to `a₁`
  · exact hnotv a₁ j1 ha1
  · refine ⟨S.gcell (t1 + n + 1) (r + 1) 0, HexDir.W, Relation.ReflTransGen.refl, ?_⟩
    rw [S.gcell_nbr_W, show t1 + (n : ℤ) + 1 - 1 = t1 + n from by ring]
    exact S.sameStack_gcell_block ha1 le_rfl (by positivity) hs1 (by omega) (by omega) hb1 ht1
  -- `v` is adjacent to `a₂`
  · exact hnotv a₂ j2 ha2
  · refine ⟨S.gcell (t2 - 1) (r + 1) 0, HexDir.E, ?_, ?_⟩
    · exact S.sameStack_gcell_gap le_rfl (by positivity) le_rfl (by positivity)
        (fun z hz => hallgap z (by omega) (by omega))
    · rw [S.gcell_nbr_E, show t2 - 1 + 1 = t2 from by ring]
      exact S.sameStack_gcell_block ha2 le_rfl (by positivity) hs2 le_rfl (by omega) hb2 ht2
  -- `v` is adjacent to `a₃`
  · exact hnotv _ jy ha3
  · refine ⟨S.gcell (t1 + n + 1) (r + 1) n, HexDir.NW, ?_, ?_⟩
    · exact S.sameStack_gcell_gap le_rfl (by positivity) (by positivity) le_rfl
        (fun z hz => hallgap z (by omega) (by omega))
    · rw [S.gcell_nbr_NW_top]
      exact S.sameStack_gcell_block ha3 le_rfl (by positivity) hs3 (by omega) (by omega) hb3
        (by rw [S.shearCol_gcell])

/-! ### The main theorem -/

/-- **The tiling described by a block schematic forms a weave pattern.**  This is the content of
the schematics of Section 2.3 of the paper (Figure 21): they are exactly the pictures of the
weave-pattern tilings. -/
theorem toTiling_isWeavePattern : S.toTiling.IsWeavePattern HexDir.W where
  horizontal_or_slantsLeft c := by
    rcases S.dirAt_eq_three c with hd | hd | hd
    · exact Or.inl hd
    · exact Or.inr (Or.inl (by rw [toTiling_dir, hd]; decide))
    · exact Or.inr (Or.inr (by rw [toTiling_dir, hd]; decide))
  exists_horizontal := by
    obtain ⟨x, hx⟩ := S.exists_gap (0 + 1)
    obtain ⟨j, -, -, hj⟩ := S.slot_overlap 0 x hx
    exact ⟨S.gcell x 0 0, S.dirAt_block (by rw [S.slotAt_gcell le_rfl (by positivity)]; exact hj)⟩
  horizontal_leftLeaning c hcd := by
    obtain ⟨j, hc⟩ := S.exists_block_of_dirAt_W hcd
    have h4 := S.four_le
    have h0 := S.subOf_nonneg c
    have hn := S.subOf_le c
    by_cases hs : S.subOf c < n
    · exact ⟨c, nbr c HexDir.NW, Relation.ReflTransGen.refl, HexDir.NW, S.stackedBy_NW hc hs,
        Or.inr (by rw [toTiling_dir, S.dirAt_block hc]; decide)⟩
    · exact ⟨c, nbr c HexDir.SE, Relation.ReflTransGen.refl, HexDir.SE,
        S.stackedBy_SE hc (by omega), Or.inl (by rw [toTiling_dir, S.dirAt_block hc]; decide)⟩
  slantsLeft_rightLeaning c hsl := by
    have hgap : (S.slotAt c).IsGap := by
      refine S.isGap_of_dirAt_ne_W ?_
      rcases hsl with h | h <;> rw [toTiling_dir] at h <;> rw [h] <;> decide
    cases hcs : S.slotAt c with
    | block _ => rw [hcs] at hgap; exact hgap.elim
    | gapL =>
      have hE : (S.slotAt (nbr c HexDir.E)).IsGap := by
        rw [S.slotAt_nbr_E]
        rcases S.succ_of_gapL hcs with h | h <;> rw [h] <;> trivial
      exact ⟨c, nbr c HexDir.E, Relation.ReflTransGen.refl, HexDir.E, S.stackedBy_E hgap hE,
        Or.inl (by rw [toTiling_dir, S.dirAt_gapL hcs]; decide)⟩
    | gapR =>
      have hE : (S.slotAt (nbr c HexDir.W)).IsGap := by
        rw [S.slotAt_nbr_W]
        rcases S.pred_of_gapR (x := shearCol c - 1)
          (by rw [show shearCol c - 1 + 1 = shearCol c from by ring]; exact hcs) with h | h <;>
          rw [h] <;> trivial
      exact ⟨c, nbr c HexDir.W, Relation.ReflTransGen.refl, HexDir.W, S.stackedBy_W hgap hE,
        Or.inl (by rw [toTiling_dir, S.dirAt_gapR hcs]; decide)⟩
  horizontal_height c hcd := by
    obtain ⟨j, hc⟩ := S.exists_block_of_dirAt_W hcd
    exact S.stackHeight_block hc
  two_above_two_below c hcd := by
    obtain ⟨j, hc⟩ := S.exists_block_of_dirAt_W hcd
    exact ⟨S.two_above hc, S.two_below hc⟩
  overlap c c' hcd hc'd hab := by
    obtain ⟨j, hc⟩ := S.exists_block_of_dirAt_W hcd
    obtain ⟨jc', hc'⟩ := S.exists_block_of_dirAt_W hc'd
    exact S.overlap_of hc hc' hab
  grid_cell c a₁ a₂ hcd h1d h2d hab1 hab2 hne := by
    obtain ⟨j, hc⟩ := S.exists_block_of_dirAt_W hcd
    obtain ⟨j1, ha1⟩ := S.exists_block_of_dirAt_W h1d
    obtain ⟨j2, ha2⟩ := S.exists_block_of_dirAt_W h2d
    obtain ⟨col1, hcol11, hcol12, hb1, hs11, hs12⟩ := S.stackAbove_col hc ha1 hab1
    obtain ⟨col2, hcol21, hcol22, hb2, hs21, hs22⟩ := S.stackAbove_col hc ha2 hab2
    have hlt : shearCol a₁ - j1 ≠ shearCol a₂ - j2 := by
      intro h
      exact hne ((S.sameStack_block_iff ha1 ha2).2 ⟨by rw [hb1, hb2], h⟩)
    rcases lt_or_gt_of_ne hlt with h | h
    · obtain ⟨a₃, v, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        S.grid_cell_ordered hc rfl rfl ha1 hb1 rfl ha2 hb2 rfl (by omega) (by omega) h
      exact ⟨a₃, v, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    · obtain ⟨a₃, v, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        S.grid_cell_ordered hc rfl rfl ha2 hb2 rfl ha1 hb1 rfl (by omega) (by omega) h
      exact ⟨a₃, v, h1, h3, h2, h4, h5, h6, h8, h7, h9⟩
  no_back_to_back v v' hvd hst hv'd := by
    have hvgap : S.slotAt v = .gapR := by
      rcases S.dirAt_cases v with ⟨jj, hj, hd⟩ | ⟨-, hd⟩ | ⟨hs, -⟩
      · rw [toTiling_dir, hd] at hvd; exact absurd hvd (by decide)
      · rw [toTiling_dir, hd] at hvd; exact absurd hvd (by decide)
      · exact hs
    have hv'gap : S.slotAt v' = .gapL := by
      rcases S.dirAt_cases v' with ⟨jj, hj, hd⟩ | ⟨hs, -⟩ | ⟨-, hd⟩
      · rw [toTiling_dir, hd] at hv'd; exact absurd hv'd (by decide)
      · exact hs
      · rw [toTiling_dir, hd] at hv'd; exact absurd hv'd (by decide)
    obtain ⟨-, -, hmem⟩ := hst
    have hE : (HexDir.W + 3 : HexDir) = HexDir.E := by decide
    rw [hE] at hmem
    have hgv : (S.slotAt v).IsGap := by rw [hvgap]; trivial
    have hgv' : (S.slotAt v').IsGap := by rw [hv'gap]; trivial
    have hbot := hmem _ (S.bot_mem_stickOf hgv)
    rw [S.mem_stickOf_gap_iff hgv'] at hbot
    simp only [shearCol_nbr_E, shearCol_shearCell, bandOf, shearRow_nbr_E,
      shearRow_shearCell] at hbot
    have hband : S.bandOf v' = S.bandOf v := by
      have h1 : bandRow n (((n : ℤ) + 1) * bandRow n (shearRow v)) = bandRow n (shearRow v) := by
        rw [show ((n : ℤ) + 1) * bandRow n (shearRow v)
            = ((n : ℤ) + 1) * bandRow n (shearRow v) + 0 from by ring]
        exact bandRow_eq n _ _ le_rfl (by positivity)
      show bandRow n (shearRow v') = bandRow n (shearRow v)
      rw [← hbot.2, h1]
    have hslot : S.slot (S.bandOf v) (shearCol v + 1) = .gapL := by
      rw [hbot.1, ← hband, ← slotAt_eq]
      exact hv'gap
    rcases S.succ_of_gapR hvgap with h | h <;> rw [h] at hslot <;> exact Slot.noConfusion hslot

/-- The tiling described by a block schematic forms a weave pattern. -/
theorem toTiling_formsWeavePattern : S.toTiling.FormsWeavePattern :=
  ⟨HexDir.W, S.toTiling_isWeavePattern⟩

/-! ### Distinct schematics describe distinct tilings -/

lemma slotAt_gapL_of_dirAt_SE {c : Hex} (h : S.dirAt c = HexDir.SE) : S.slotAt c = .gapL := by
  rcases S.dirAt_cases c with ⟨-, -, hd⟩ | ⟨hs, -⟩ | ⟨-, hd⟩
  · rw [hd] at h; exact absurd h (by decide)
  · exact hs
  · rw [hd] at h; exact absurd h (by decide)

lemma slotAt_gapR_of_dirAt_NW {c : Hex} (h : S.dirAt c = HexDir.NW) : S.slotAt c = .gapR := by
  rcases S.dirAt_cases c with ⟨-, -, hd⟩ | ⟨-, hd⟩ | ⟨hs, -⟩
  · rw [hd] at h; exact absurd h (by decide)
  · rw [hd] at h; exact absurd h (by decide)
  · exact hs

/-- A schematic is determined by the tiling it describes: the correspondence between schematics
with blocks of length `n` and the weave-pattern tilings by sticks of length `n + 1` is
one-to-one. -/
theorem toTiling_injective {S S' : Schematic n} (h : S.toTiling = S'.toTiling) : S = S' := by
  have key : ∀ r x : ℤ, S.slot r x = S'.slot r x := by
    intro r x
    have hs : S.slotAt (S.gcell x r 0) = S.slot r x := S.slotAt_gcell le_rfl (by positivity) x r
    have hs' : S'.slotAt (S.gcell x r 0) = S'.slot r x :=
      S'.slotAt_gcell le_rfl (by positivity) x r
    have hd : S.dirAt (S.gcell x r 0) = S'.dirAt (S.gcell x r 0) := by
      have hh := congrArg (fun T => T.dir (S.gcell x r 0)) h
      simpa using hh
    have hi : S.idxAt (S.gcell x r 0) = S'.idxAt (S.gcell x r 0) := by
      have hh := congrArg (fun T => T.idx (S.gcell x r 0)) h
      simpa using hh
    rw [← hs, ← hs']
    cases hS : S.slotAt (S.gcell x r 0) with
    | block j =>
      have hjn := S.slotAt_block_le hS
      obtain ⟨j', hS'⟩ := S'.exists_block_of_dirAt_W (by rw [← hd, S.dirAt_block hS])
      have hj'n := S'.slotAt_block_le hS'
      rw [S.idxAt_block hS, S'.idxAt_block hS'] at hi
      rw [hS']
      congr 1
      omega
    | gapL => rw [S'.slotAt_gapL_of_dirAt_SE (by rw [← hd, S.dirAt_gapL hS])]
    | gapR => rw [S'.slotAt_gapR_of_dirAt_NW (by rw [← hd, S.dirAt_gapR hS])]
  obtain ⟨sl, hstep, hov⟩ := S
  obtain ⟨sl', hstep', hov'⟩ := S'
  have hsl : sl = sl' := funext fun r => funext fun x => key r x
  subst hsl
  rfl

end Schematic

end StickPolyhex
