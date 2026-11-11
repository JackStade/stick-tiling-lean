import Tiling.Proofs.SchematicStackSets
import Tiling.Proofs.SchematicRows

/-!
# Stacks lying above and below one another

This file prepares the proof that the tiling of a schematic forms a weave pattern.  It provides

* `Schematic.gcell`: the cell of the grid in a given column, at a given height inside a given
  band, together with its basic data;
* `Schematic.sameStack_block_iff`: two cells of blocks lie in the same stack exactly when the
  blocks have the same band and the same leftmost column;
* `Schematic.stackAbove_col` and `Schematic.stackBelow_col`: a horizontal stack lying above (or
  below) the stack of a block sits in the next (or previous) band and meets the window of
  columns spanned by that block, widened by one column on the appropriate side.
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-! ### Cells given by column, band and height in the band -/

/-- The cell in the column `y` of the grid, at height `i` in the band `r`. -/
def gcell (_S : Schematic n) (y r i : ℤ) : Hex := shearCell y (((n : ℤ) + 1) * r + i)

@[simp] lemma shearCol_gcell (y r i : ℤ) : shearCol (S.gcell y r i) = y :=
  shearCol_shearCell _ _

@[simp] lemma shearRow_gcell (y r i : ℤ) : shearRow (S.gcell y r i) = ((n : ℤ) + 1) * r + i := rfl

lemma bandOf_gcell {i : ℤ} (h0 : 0 ≤ i) (hi : i ≤ n) (y r : ℤ) : S.bandOf (S.gcell y r i) = r :=
  bandRow_eq n _ _ h0 hi

lemma subOf_gcell {i : ℤ} (h0 : 0 ≤ i) (hi : i ≤ n) (y r : ℤ) : S.subOf (S.gcell y r i) = i :=
  subRow_eq n _ _ h0 hi

lemma slotAt_gcell {i : ℤ} (h0 : 0 ≤ i) (hi : i ≤ n) (y r : ℤ) :
    S.slotAt (S.gcell y r i) = S.slot r y := by
  rw [slotAt_eq, shearCol_gcell, S.bandOf_gcell h0 hi]

/-! ### Neighbours of these cells -/

lemma gcell_nbr_NW_top (y r : ℤ) : nbr (S.gcell y r n) HexDir.NW = S.gcell y (r + 1) 0 :=
  hex_ext (by simp [gcell]) (by simp [gcell]; ring)

lemma gcell_nbr_NE_top (y r : ℤ) : nbr (S.gcell y r n) HexDir.NE = S.gcell (y + 1) (r + 1) 0 :=
  hex_ext (by simp [gcell]) (by simp [gcell]; ring)

lemma gcell_nbr_SE_bot (y r : ℤ) : nbr (S.gcell y r 0) HexDir.SE = S.gcell y (r - 1) n :=
  hex_ext (by simp [gcell]) (by simp [gcell]; ring)

lemma gcell_nbr_SW_bot (y r : ℤ) : nbr (S.gcell y r 0) HexDir.SW = S.gcell (y - 1) (r - 1) n :=
  hex_ext (by simp [gcell]) (by simp [gcell]; ring)

lemma gcell_nbr_E (y r i : ℤ) : nbr (S.gcell y r i) HexDir.E = S.gcell (y + 1) r i :=
  hex_ext (by simp [gcell]) (by simp [gcell])

lemma gcell_nbr_W (y r i : ℤ) : nbr (S.gcell y r i) HexDir.W = S.gcell (y - 1) r i :=
  hex_ext (by simp [gcell]) (by simp [gcell])

/-! ### Recognising the stacks -/

/-- Two cells of blocks lie in the same stack exactly when their blocks have the same band and
the same leftmost column. -/
lemma sameStack_block_iff {a b : Hex} {ja jb : ℕ} (ha : S.slotAt a = .block ja)
    (hb : S.slotAt b = .block jb) :
    S.toTiling.SameStack a b ↔ S.bandOf a = S.bandOf b ∧ shearCol a - ja = shearCol b - jb := by
  rw [S.sameStack_iff]
  constructor
  · rintro (⟨ja', jb', ha', hb', hband, hcol⟩ | ⟨hg, -, -, -⟩)
    · rw [ha] at ha'; rw [hb] at hb'
      injection ha' with e1
      injection hb' with e2
      subst e1; subst e2
      exact ⟨hband, hcol⟩
    · rw [ha] at hg; exact hg.elim
  · rintro ⟨hband, hcol⟩
    exact Or.inl ⟨ja, jb, ha, hb, hband, hcol⟩

/-- A cell of a block and a cell of a gap never lie in the same stack. -/
lemma not_sameStack_block_gap {a b : Hex} {ja : ℕ} (ha : S.slotAt a = .block ja)
    (hb : (S.slotAt b).IsGap) : ¬ S.toTiling.SameStack a b := by
  intro h
  rcases (S.sameStack_iff a b).1 h with ⟨-, jb, -, hb', -, -⟩ | ⟨hg, -, -, -⟩
  · rw [hb'] at hb; exact hb.elim
  · rw [ha] at hg; exact hg.elim

/-- Cells of gaps of one band with only gap columns in between lie in the same stack. -/
lemma sameStack_gap_of {a b : Hex} (ha : (S.slotAt a).IsGap) (hb : (S.slotAt b).IsGap)
    (hband : S.bandOf a = S.bandOf b)
    (hy : ∀ y : ℤ, ((shearCol a ≤ y ∧ y ≤ shearCol b) ∨ (shearCol b ≤ y ∧ y ≤ shearCol a)) →
      (S.slot (S.bandOf a) y).IsGap) : S.toTiling.SameStack a b :=
  (S.sameStack_iff a b).2 (Or.inr ⟨ha, hb, hband, hy⟩)

/-- The data carried by a cell lying in the same stack as a cell of a block. -/
lemma block_data_of_sameStack {a x : Hex} {ja : ℕ} (ha : S.slotAt a = .block ja)
    (h : S.toTiling.SameStack a x) :
    ∃ jx, S.slotAt x = .block jx ∧ S.bandOf a = S.bandOf x ∧
      shearCol a - ja = shearCol x - jx := by
  rcases (S.sameStack_iff a x).1 h with ⟨ja', jx, ha', hx, hband, hcol⟩ | ⟨hg, -, -, -⟩
  · rw [ha] at ha'
    injection ha' with e
    subst e
    exact ⟨jx, hx, hband, hcol⟩
  · rw [ha] at hg; exact hg.elim

/-! ### Stacks above -/

/-- The core of `Schematic.stackAbove_col`. -/
lemma stackAbove_aux {c a x z : Hex} {j ja : ℕ} (hc : S.slotAt c = .block j)
    (ha : S.slotAt a = .block ja) (hne : ¬ S.toTiling.SameStack c a)
    (hbandx : S.bandOf c = S.bandOf x)
    (haz : S.toTiling.SameStack a z) (hrowz : shearRow z = shearRow x + 1)
    (hz1 : shearCol c - j ≤ shearCol z) (hz2 : shearCol z ≤ shearCol c - j + n + 1) :
    ∃ col : ℤ, shearCol c - j ≤ col ∧ col ≤ shearCol c - j + n + 1 ∧
      S.bandOf a = S.bandOf c + 1 ∧ shearCol a - ja ≤ col ∧ col ≤ shearCol a - ja + n := by
  obtain ⟨jz, hjz, hbandaz, hcolaz⟩ := S.block_data_of_sameStack ha haz
  have hjzn := S.slotAt_block_le hjz
  have hstart : S.slot (S.bandOf c) (shearCol c - j) = .block 0 := S.slot_block_start hc
  have hsub0 := S.subOf_nonneg x
  have hsubn := S.subOf_le x
  by_cases hi : S.subOf x < n
  · exfalso
    have hbz : S.bandOf z = S.bandOf x := by
      rw [bandOf, hrowz, (bandRow_succ_of_lt (n := n) hi).1, bandOf]
    have hslotz : S.slot (S.bandOf c) (shearCol z) = .block jz := by
      rw [← hjz, slotAt_eq, hbz, hbandx]
    by_cases hcase : shearCol z ≤ shearCol c - j + n
    · have hb := S.slot_of_start hstart hz1 hcase
      rw [hslotz] at hb
      injection hb with e
      refine hne ((S.sameStack_block_iff hc ha).2 ⟨?_, ?_⟩)
      · rw [hbandaz, hbz, ← hbandx]
      · rw [hcolaz]; omega
    · have hcolz : shearCol z = shearCol c - j + n + 1 := by omega
      have hgL : S.slot (S.bandOf c) (shearCol c - j + n + 1) = .gapL := S.slot_gapL_of_block hc
      rw [hcolz, hgL] at hslotz
      exact Slot.noConfusion hslotz
  · have hin : S.subOf x = n := by omega
    have hbz : S.bandOf z = S.bandOf x + 1 := by
      rw [bandOf, hrowz, bandRow_succ_of_eq_n (n := n) (show subRow n (shearRow x) = n from hin),
        bandOf]
    exact ⟨shearCol z, hz1, hz2, by rw [hbandaz, hbz, ← hbandx], by omega, by omega⟩

/-- A horizontal stack lying above the stack of a block sits in the next band and meets the
window of columns of that block, widened by one column on the right. -/
lemma stackAbove_col {c a : Hex} {j ja : ℕ} (hc : S.slotAt c = .block j)
    (ha : S.slotAt a = .block ja) (hab : S.toTiling.StackAbove HexDir.W c a) :
    ∃ col : ℤ, shearCol c - j ≤ col ∧ col ≤ shearCol c - j + n + 1 ∧
      S.bandOf a = S.bandOf c + 1 ∧ shearCol a - ja ≤ col ∧ col ≤ shearCol a - ja + n := by
  obtain ⟨hne, x, hcx, hz⟩ := hab
  obtain ⟨jx, hjx, hbandx, hcolx⟩ := S.block_data_of_sameStack hc hcx
  have hjxn := S.slotAt_block_le hjx
  have hW4 : (HexDir.W + 4 : HexDir) = HexDir.NE := by decide
  have hW5 : (HexDir.W + 5 : HexDir) = HexDir.NW := by decide
  rcases hz with h4 | h5
  · rw [hW4] at h4
    exact S.stackAbove_aux hc ha hne hbandx h4 (by simp) (by simp; omega) (by simp; omega)
  · rw [hW5] at h5
    exact S.stackAbove_aux hc ha hne hbandx h5 (by simp) (by simp; omega) (by simp; omega)

/-! ### Stacks below -/

/-- The core of `Schematic.stackBelow_col`. -/
lemma stackBelow_aux {c a x z : Hex} {j ja : ℕ} (hc : S.slotAt c = .block j)
    (ha : S.slotAt a = .block ja) (hne : ¬ S.toTiling.SameStack c a)
    (hbandx : S.bandOf c = S.bandOf x)
    (haz : S.toTiling.SameStack a z) (hrowz : shearRow z = shearRow x - 1)
    (hz1 : shearCol c - j - 1 ≤ shearCol z) (hz2 : shearCol z ≤ shearCol c - j + n) :
    ∃ col : ℤ, shearCol c - j - 1 ≤ col ∧ col ≤ shearCol c - j + n ∧
      S.bandOf a = S.bandOf c - 1 ∧ shearCol a - ja ≤ col ∧ col ≤ shearCol a - ja + n := by
  obtain ⟨jz, hjz, hbandaz, hcolaz⟩ := S.block_data_of_sameStack ha haz
  have hjzn := S.slotAt_block_le hjz
  have hstart : S.slot (S.bandOf c) (shearCol c - j) = .block 0 := S.slot_block_start hc
  have hsub0 := S.subOf_nonneg x
  have hsubn := S.subOf_le x
  by_cases hi : 0 < S.subOf x
  · exfalso
    have hbz : S.bandOf z = S.bandOf x := by
      rw [bandOf, hrowz, (bandRow_pred_of_pos (n := n) hi).1, bandOf]
    have hslotz : S.slot (S.bandOf c) (shearCol z) = .block jz := by
      rw [← hjz, slotAt_eq, hbz, hbandx]
    by_cases hcase : shearCol c - j ≤ shearCol z
    · have hb := S.slot_of_start hstart hcase hz2
      rw [hslotz] at hb
      injection hb with e
      refine hne ((S.sameStack_block_iff hc ha).2 ⟨?_, ?_⟩)
      · rw [hbandaz, hbz, ← hbandx]
      · rw [hcolaz]; omega
    · have hcolz : shearCol z = shearCol c - j - 1 := by omega
      have hgR : S.slot (S.bandOf c) (shearCol c - j - 1) = .gapR := S.slot_gapR_of_block hc
      rw [hcolz, hgR] at hslotz
      exact Slot.noConfusion hslotz
  · have hin : S.subOf x = 0 := by omega
    have hbz : S.bandOf z = S.bandOf x - 1 := by
      rw [bandOf, hrowz, bandRow_pred_of_eq_zero (n := n)
        (show subRow n (shearRow x) = 0 from hin), bandOf]
    exact ⟨shearCol z, hz1, hz2, by rw [hbandaz, hbz, ← hbandx], by omega, by omega⟩

/-- A horizontal stack lying below the stack of a block sits in the previous band and meets the
window of columns of that block, widened by one column on the left. -/
lemma stackBelow_col {c a : Hex} {j ja : ℕ} (hc : S.slotAt c = .block j)
    (ha : S.slotAt a = .block ja) (hab : S.toTiling.StackBelow HexDir.W c a) :
    ∃ col : ℤ, shearCol c - j - 1 ≤ col ∧ col ≤ shearCol c - j + n ∧
      S.bandOf a = S.bandOf c - 1 ∧ shearCol a - ja ≤ col ∧ col ≤ shearCol a - ja + n := by
  obtain ⟨hne, x, hcx, hz⟩ := hab
  obtain ⟨jx, hjx, hbandx, hcolx⟩ := S.block_data_of_sameStack hc hcx
  have hjxn := S.slotAt_block_le hjx
  have hW1 : (HexDir.W + 1 : HexDir) = HexDir.SW := by decide
  have hW2 : (HexDir.W + 2 : HexDir) = HexDir.SE := by decide
  rcases hz with h1 | h2
  · rw [hW1] at h1
    exact S.stackBelow_aux hc ha hne hbandx h1 (by simp) (by simp; omega) (by simp; omega)
  · rw [hW2] at h2
    exact S.stackBelow_aux hc ha hne hbandx h2 (by simp) (by simp; omega) (by simp; omega)


/-! ### Convenient recognisers for cells given by column and band -/

/-- The slot of a cell of the block of a row starting at the column `s`. -/
lemma slotAt_gcell_block {y r i s : ℤ} (h0 : 0 ≤ i) (hi : i ≤ n) (hs : S.slot r s = .block 0)
    (hy1 : s ≤ y) (hy2 : y ≤ s + n) : S.slotAt (S.gcell y r i) = .block ((y - s).toNat) := by
  rw [S.slotAt_gcell h0 hi]
  exact S.slot_of_start hs hy1 hy2

lemma dirAt_gcell_block {y r i s : ℤ} (h0 : 0 ≤ i) (hi : i ≤ n) (hs : S.slot r s = .block 0)
    (hy1 : s ≤ y) (hy2 : y ≤ s + n) : S.dirAt (S.gcell y r i) = HexDir.W :=
  S.dirAt_block (S.slotAt_gcell_block h0 hi hs hy1 hy2)

/-- A cell of a block lies in the same stack as any cell of the same block. -/
lemma sameStack_gcell_block {a : Hex} {ja : ℕ} (ha : S.slotAt a = .block ja)
    {y r i s : ℤ} (h0 : 0 ≤ i) (hi : i ≤ n) (hs : S.slot r s = .block 0)
    (hy1 : s ≤ y) (hy2 : y ≤ s + n) (hband : S.bandOf a = r)
    (hstart : shearCol a - ja = s) : S.toTiling.SameStack a (S.gcell y r i) := by
  refine (S.sameStack_block_iff ha (S.slotAt_gcell_block h0 hi hs hy1 hy2)).2 ⟨?_, ?_⟩
  · rw [hband, S.bandOf_gcell h0 hi]
  · rw [hstart, S.shearCol_gcell]; omega

/-- Two cells of one gap lie in the same stack. -/
lemma sameStack_gcell_gap {y y' r i i' : ℤ} (h0 : 0 ≤ i) (hi : i ≤ n) (h0' : 0 ≤ i')
    (hi' : i' ≤ n) (hy : ∀ z : ℤ, ((y ≤ z ∧ z ≤ y') ∨ (y' ≤ z ∧ z ≤ y)) → (S.slot r z).IsGap) :
    S.toTiling.SameStack (S.gcell y r i) (S.gcell y' r i') := by
  have hgy : (S.slot r y).IsGap := by
    rcases le_total y y' with h | h
    · exact hy y (Or.inl ⟨le_rfl, h⟩)
    · exact hy y (Or.inr ⟨h, le_rfl⟩)
  have hgy' : (S.slot r y').IsGap := by
    rcases le_total y y' with h | h
    · exact hy y' (Or.inl ⟨h, le_rfl⟩)
    · exact hy y' (Or.inr ⟨le_rfl, h⟩)
  refine S.sameStack_gap_of (by rw [S.slotAt_gcell h0 hi]; exact hgy)
    (by rw [S.slotAt_gcell h0' hi']; exact hgy')
    (by rw [S.bandOf_gcell h0 hi, S.bandOf_gcell h0' hi']) ?_
  intro z hz
  rw [S.bandOf_gcell h0 hi]
  rw [S.shearCol_gcell, S.shearCol_gcell] at hz
  exact hy z hz

end Schematic

end StickPolyhex
