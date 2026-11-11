import Tiling.Proofs.WeaveAlign

/-!
# Every weave-pattern tiling is described by a schematic

This file proves the converse of `Schematic.toTiling_isWeavePattern`: a tiling by sticks of
length `n + 1` (with `n ≥ 4`) which satisfies the weave rules and is normalised so that its
horizontal sticks point west is, up to a translation, the tiling described by a block schematic
with blocks of length `n`.

The schematic is read off the tiling: the alignment of the bands provided by
`StickTiling.bandBase_congr` gives a row `b` at which every block and every left-slanting stick
of the tiling starts, and the slot of the column `x` of the row `r` of the schematic is read at
the cell of column `x` in the row `b + (n+1) * r`, the bottom row of the band.
-/

namespace StickPolyhex

/-- The tiling obtained by translating `T` by the vector `v`. -/
def StickTiling.translate {n : ℕ} (T : StickTiling n) (v : Hex) : StickTiling n where
  dir c := T.dir (c + v)
  idx c := T.idx (c + v)
  idx_pos c := T.idx_pos _
  idx_le c := T.idx_le _
  succ_dir c h := by
    have : nbr c (T.dir (c + v)) + v = nbr (c + v) (T.dir (c + v)) := by
      simp [nbr]; abel
    rw [this]; exact T.succ_dir _ h
  succ_idx c h := by
    have : nbr c (T.dir (c + v)) + v = nbr (c + v) (T.dir (c + v)) := by
      simp [nbr]; abel
    rw [this]; exact T.succ_idx _ h
  pred_dir c h := by
    have : nbr c (T.dir (c + v)).opp + v = nbr (c + v) (T.dir (c + v)).opp := by
      simp [nbr]; abel
    rw [this]; exact T.pred_dir _ h
  pred_idx c h := by
    have : nbr c (T.dir (c + v)).opp + v = nbr (c + v) (T.dir (c + v)).opp := by
      simp [nbr]; abel
    rw [this]; exact T.pred_idx _ h

@[simp] lemma StickTiling.translate_dir {n : ℕ} (T : StickTiling n) (v c : Hex) :
    (T.translate v).dir c = T.dir (c + v) := rfl

@[simp] lemma StickTiling.translate_idx {n : ℕ} (T : StickTiling n) (v c : Hex) :
    (T.translate v).idx c = T.idx (c + v) := rfl

/-- Two stick tilings with the same orientations and the same indices are equal. -/
lemma StickTiling.ext' {n : ℕ} {T T' : StickTiling n} (hd : ∀ c, T.dir c = T'.dir c)
    (hi : ∀ c, T.idx c = T'.idx c) : T = T' := by
  cases T; cases T'
  simp only [mk.injEq]
  exact ⟨funext hd, funext hi⟩

namespace StickTiling

variable {n : ℕ} (T : StickTiling (n + 1))

/-! ### Reading a slot off the tiling -/

/-- The slot described by a cell: a horizontal cell is the `n + 1 - idx`-th column of a block, a
cell of a stick pointing south-east is a column of the left part of a gap, and a cell of a stick
pointing north-west is a column of the right part of a gap. -/
def slotOfCell (c : Hex) : Slot :=
  if T.dir c = HexDir.W then .block (n + 1 - T.idx c)
  else if T.dir c = HexDir.SE then .gapL else .gapR

/-- The cell of the column `x` in the bottom row of the band `r`, for a tiling by sticks of
length `n + 1` whose bands start at the row `b`. -/
def refCell (n : ℕ) (b r x : ℤ) : Hex := shearCell x (b + ((n : ℤ) + 1) * r)

/-! ### Climbing inside a band -/

/-- **Climbing a band.**  Starting from a cell at the bottom of its band, the cell `k` rows
higher (in the same column) belongs to the same block or to the same left-slanting stick: it is
covered in the same direction and lies `k` rows above the bottom of the band. -/
theorem climb_dir_phi (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    {z : Hex} (hz : T.phi z = 0) (k : ℕ) (hk : k ≤ n) :
    T.dir (walk z HexDir.NW k) = T.dir z ∧ T.phi (walk z HexDir.NW k) = k := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    obtain ⟨hdk, hpk⟩ := ih (by omega)
    have hstep : walk z HexDir.NW ((k + 1 : ℕ) : ℤ) = nbr (walk z HexDir.NW (k : ℤ)) HexDir.NW :=
      walk_nat_succ z HexDir.NW k
    have hlt : T.phi (walk z HexDir.NW (k : ℤ)) + 1 < ((n + 1 : ℕ) : ℤ) := by
      rw [hpk]; push_cast; omega
    obtain ⟨hd', hp', -⟩ := T.data_up hv (by omega) hw (walk z HexDir.NW (k : ℤ)) hlt
    refine ⟨by rw [hstep, hd', hdk], by rw [hstep, hp', hpk]; push_cast; ring⟩

/-- Climbing a band inside a block: the index does not change. -/
theorem climb_idx_W (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    {z : Hex} (hz : T.phi z = 0) (hd : T.dir z = HexDir.W) (k : ℕ) (hk : k ≤ n) :
    T.idx (walk z HexDir.NW k) = T.idx z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hik := ih (by omega)
    obtain ⟨hdk, hpk⟩ := T.climb_dir_phi hv hn hw hz k (by omega)
    have hstep : walk z HexDir.NW ((k + 1 : ℕ) : ℤ) = nbr (walk z HexDir.NW (k : ℤ)) HexDir.NW :=
      walk_nat_succ z HexDir.NW k
    have hlt : T.phi (walk z HexDir.NW (k : ℤ)) + 1 < ((n + 1 : ℕ) : ℤ) := by
      rw [hpk]; push_cast; omega
    obtain ⟨-, -, hi'⟩ := T.data_up hv (by omega) hw (walk z HexDir.NW (k : ℤ)) hlt
    rw [hstep, hi', if_pos (by rw [hdk, hd]), hik]

/-- Climbing a band along a stick pointing north-west: the index increases. -/
theorem climb_idx_NW (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    {z : Hex} (hz : T.phi z = 0) (hd : T.dir z = HexDir.NW) (k : ℕ) (hk : k ≤ n) :
    T.idx (walk z HexDir.NW k) = T.idx z + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hik := ih (by omega)
    obtain ⟨hdk, hpk⟩ := T.climb_dir_phi hv hn hw hz k (by omega)
    have hstep : walk z HexDir.NW ((k + 1 : ℕ) : ℤ) = nbr (walk z HexDir.NW (k : ℤ)) HexDir.NW :=
      walk_nat_succ z HexDir.NW k
    have hlt : T.phi (walk z HexDir.NW (k : ℤ)) + 1 < ((n + 1 : ℕ) : ℤ) := by
      rw [hpk]; push_cast; omega
    obtain ⟨-, -, hi'⟩ := T.data_up hv (by omega) hw (walk z HexDir.NW (k : ℤ)) hlt
    rw [hstep, hi', if_neg (by rw [hdk, hd]; decide), if_pos (by rw [hdk, hd]), hik]
    omega

/-- Climbing a band along a stick pointing south-east: the index decreases. -/
theorem climb_idx_SE (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    {z : Hex} (hz : T.phi z = 0) (hd : T.dir z = HexDir.SE) (k : ℕ) (hk : k ≤ n) :
    T.idx (walk z HexDir.NW k) = T.idx z - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hik := ih (by omega)
    obtain ⟨hdk, hpk⟩ := T.climb_dir_phi hv hn hw hz k (by omega)
    have hstep : walk z HexDir.NW ((k + 1 : ℕ) : ℤ) = nbr (walk z HexDir.NW (k : ℤ)) HexDir.NW :=
      walk_nat_succ z HexDir.NW k
    have hlt : T.phi (walk z HexDir.NW (k : ℤ)) + 1 < ((n + 1 : ℕ) : ℤ) := by
      rw [hpk]; push_cast; omega
    obtain ⟨-, -, hi'⟩ := T.data_up hv (by omega) hw (walk z HexDir.NW (k : ℤ)) hlt
    rw [hstep, hi', if_neg (by rw [hdk, hd]; decide), if_neg (by rw [hdk, hd]; decide), hik]
    omega

/-! ### The schematic read off the tiling -/

/-- The cell at which the slot of the column `x` of the row `r` is read lies at the bottom of its
band. -/
theorem phi_refCell (hn : 4 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    {b : ℤ} (hb : ∀ c, ((n : ℤ) + 1) ∣ T.bandBase c - b) (r x : ℤ) :
    T.phi (refCell n b r x) = 0 := by
  have hrow : shearRow (refCell n b r x) = b + ((n : ℤ) + 1) * r := by
    rw [refCell, shearRow_shearCell]
  have hdvd : ((n : ℤ) + 1) ∣ T.phi (refCell n b r x) := by
    have h := hb (refCell n b r x)
    have hb' : T.bandBase (refCell n b r x) =
        shearRow (refCell n b r x) - T.phi (refCell n b r x) := rfl
    rw [hb', hrow] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨r - m, ?_⟩
    have hexp : ((n : ℤ) + 1) * (r - m) = ((n : ℤ) + 1) * r - ((n : ℤ) + 1) * m := by ring
    rw [hexp]
    linarith [hm]
  have h0 : 0 ≤ T.phi (refCell n b r x) := T.phi_nonneg hw _
  have h1 : T.phi (refCell n b r x) < ((n + 1 : ℕ) : ℤ) := T.phi_lt hw _
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m = 0 := by
    rw [hm] at h0 h1
    push_cast at h1
    nlinarith
  rw [hm, hm0, mul_zero]

/-- The index of a cell at the bottom of its band, for a stick pointing north-west. -/
lemma idx_eq_one_of_phi_zero_NW {z : Hex} (hz : T.phi z = 0) (hd : T.dir z = HexDir.NW) :
    T.idx z = 1 := by
  rw [T.phi_of_dir_NW hd] at hz
  omega

/-- The index of a cell at the bottom of its band, for a stick pointing south-east. -/
lemma idx_eq_length_of_phi_zero_SE {z : Hex} (hz : T.phi z = 0) (hd : T.dir z = HexDir.SE) :
    T.idx z = n + 1 := by
  rw [T.phi_of_dir_SE hd] at hz
  have := T.idx_le z
  omega

/-- A cell at the bottom of its band on a left-slanting stick is the lowest cell of that
stick. -/
lemma botCell_eq_self_of_phi_zero {z : Hex} (hz : T.phi z = 0) (hs : T.Slanted z) :
    T.botCell z = z := by
  rcases hs with hd | hd
  · rw [T.botCell_of_NW hd, T.head_eq_self_of_idx_eq (T.idx_eq_one_of_phi_zero_NW hz hd)]
  · rw [T.botCell_of_SE hd, T.tail_eq_self_of_idx_eq (T.idx_eq_length_of_phi_zero_SE hz hd)]

/-- Two left-slanting sticks starting in the same row in neighbouring columns are a stacked
pair. -/
lemma stackedBy_east_of_phi_zero {z : Hex} (hz : T.phi z = 0)
    (hz' : T.phi (nbr z HexDir.E) = 0) (hs : T.Slanted z) (hs' : T.Slanted (nbr z HexDir.E)) :
    T.StackedBy z (nbr z HexDir.E) HexDir.E := by
  have h0 : 0 < n + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rcases hs with hd | hd <;> rw [hd] <;> decide
  · rcases hs with hd | hd <;> rcases hs' with hd' | hd' <;> rw [hd, hd'] <;> decide
  · intro p hp
    rw [T.stickOf_eq_image_botCell h0 hs, T.botCell_eq_self_of_phi_zero hz hs] at hp
    rw [T.stickOf_eq_image_botCell h0 hs', T.botCell_eq_self_of_phi_zero hz' hs']
    simp only [Finset.mem_image, Finset.mem_range] at hp ⊢
    obtain ⟨k, hk, rfl⟩ := hp
    exact ⟨k, hk, by rw [walk_nbr_comm]⟩

/-- The slots read off two neighbouring cells at the bottom of their band follow one another as
in a schematic. -/
theorem slotOfCell_step_cells (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {z : Hex} (hz : T.phi z = 0)
    (hz' : T.phi (nbr z HexDir.E) = 0) :
    Slot.Step n (T.slotOfCell z) (T.slotOfCell (nbr z HexDir.E)) := by
  have h0 : 0 < n + 1 := by omega
  have hback : nbr (nbr z HexDir.E) HexDir.W = z :=
    nbr_nbr_cancel z (by decide : HexDir.W = HexDir.E.opp)
  rcases T.dir_cases hw z with hd | hd | hd
  · -- a horizontal cell: the next column is the next column of the same block, or the first
    -- column of the gap in front of it
    have hslot : T.slotOfCell z = .block (n + 1 - T.idx z) := by rw [slotOfCell, if_pos hd]
    have hpos := T.idx_pos z
    have hle := T.idx_le z
    by_cases hi : T.idx z = 1
    · have hhead : T.head z = z := T.head_eq_self_of_idx_eq hi
      have hdE : T.dir (nbr z HexDir.E) = HexDir.SE := by
        have h := T.dir_frontFlank hv (by omega) (T.isLeftLeaningStack_of_dir_W hw hd) hd
        rw [frontFlank, show HexDir.W.opp = HexDir.E from by decide, hhead] at h
        simpa using h
      have hslot' : T.slotOfCell (nbr z HexDir.E) = .gapL := by
        rw [slotOfCell, if_neg (by rw [hdE]; decide), if_pos hdE]
      rw [hslot, hslot', hi]
      simp only [Slot.Step]
      omega
    · have hgt : 1 < T.idx z := by omega
      have hmem := T.nbr_dir_opp_mem_stickOf z hgt
      rw [hd, show HexDir.W.opp = HexDir.E from by decide] at hmem
      have hdE : T.dir (nbr z HexDir.E) = HexDir.W := by rw [T.dir_of_mem_stickOf hmem, hd]
      have hiE : T.idx (nbr z HexDir.E) = T.idx z - 1 := by
        have h := T.pred_idx z hgt
        rwa [hd, show HexDir.W.opp = HexDir.E from by decide] at h
      rw [hslot, slotOfCell, if_pos hdE, hiE]
      simp only [Slot.Step]
      omega
  · -- the right part of a gap: the next column is the right part again, or the first column of
    -- the next block
    have hslot : T.slotOfCell z = .gapR := by
      rw [slotOfCell, if_neg (by rw [hd]; decide), if_neg (by rw [hd]; decide)]
    rcases T.dir_cases hw (nbr z HexDir.E) with hdE | hdE | hdE
    · have hidx : T.idx (nbr z HexDir.E) = n + 1 := by
        refine T.idx_eq_n_of_nbr_W_ne hdE ?_
        rw [hback, hd]
        decide
      rw [hslot, slotOfCell, if_pos hdE, hidx]
      simp only [Slot.Step]
      omega
    · rw [hslot, slotOfCell, if_neg (by rw [hdE]; decide), if_neg (by rw [hdE]; decide)]
      trivial
    · -- excluded by the rule that no stick of a vertical stack is stacked back to back
      exfalso
      have hst : T.StackedBy z (nbr z HexDir.E) (HexDir.W + 3) := by
        rw [show HexDir.W + 3 = HexDir.E from by decide]
        exact T.stackedBy_east_of_phi_zero hz hz' (Or.inl hd) (Or.inr hdE)
      exact hw.no_back_to_back z (nbr z HexDir.E) (by rw [hd]; decide) hst (by rw [hdE]; decide)
  · -- the left part of a gap: the next column is a gap column again
    have hslot : T.slotOfCell z = .gapL := by
      rw [slotOfCell, if_neg (by rw [hd]; decide), if_pos hd]
    have hdE : T.dir (nbr z HexDir.E) ≠ HexDir.W := by
      intro hdE
      have hidx : T.idx (nbr z HexDir.E) = n + 1 := by
        refine T.idx_eq_n_of_nbr_W_ne hdE ?_
        rw [hback, hd]
        decide
      have hflank : T.flank HexDir.W (nbr z HexDir.E) = z := by
        rw [T.flank_eq_nbr_W hdE (by rw [hback, hd]; decide), hback]
      have hdflank := T.dir_flank_eq hv (by omega)
        (T.isLeftLeaningStack_of_dir_W hw hdE) hdE
      rw [hflank, hd] at hdflank
      exact absurd hdflank (by decide)
    rcases T.dir_cases hw (nbr z HexDir.E) with h | h | h
    · exact absurd h hdE
    · rw [hslot, slotOfCell, if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]
      trivial
    · rw [hslot, slotOfCell, if_neg (by rw [h]; decide), if_pos h]
      trivial

/-- Neighbouring columns of a row of the schematic are read at neighbouring cells. -/
lemma refCell_succ (b r x : ℤ) : refCell n b r (x + 1) = nbr (refCell n b r x) HexDir.E := by
  refine hex_ext ?_ ?_
  · rw [refCell, refCell, shearCol_shearCell, shearCol_nbr_E, shearCol_shearCell]
  · rw [refCell, refCell, shearRow_shearCell, shearRow_nbr_E, shearRow_shearCell]

/-- The slots read off the tiling follow one another along a row as in a schematic. -/
theorem slotOfCell_step (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {b : ℤ} (hb : ∀ c, ((n : ℤ) + 1) ∣ T.bandBase c - b)
    (r x : ℤ) :
    Slot.Step n (T.slotOfCell (refCell n b r x)) (T.slotOfCell (refCell n b r (x + 1))) := by
  rw [refCell_succ]
  refine T.slotOfCell_step_cells hv hn hw (T.phi_refCell hn hw hb r x) ?_
  rw [← refCell_succ]
  exact T.phi_refCell hn hw hb r (x + 1)

/-- A gap column of a row of the schematic read off the tiling lies strictly inside a block of
the row below. -/
theorem slotOfCell_overlap (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {b : ℤ} (hb : ∀ c, ((n : ℤ) + 1) ∣ T.bandBase c - b)
    (r x : ℤ) (hgap : (T.slotOfCell (refCell n b (r + 1) x)).IsGap) :
    ∃ j, 2 ≤ j ∧ j + 1 ≤ n ∧ T.slotOfCell (refCell n b r x) = .block j := by
  have h0 : 0 < n + 1 := by omega
  have hphi1 : T.phi (refCell n b (r + 1) x) = 0 := T.phi_refCell hn hw hb (r + 1) x
  have hphi0 : T.phi (refCell n b r x) = 0 := T.phi_refCell hn hw hb r x
  -- the gap column of the upper row carries a left-slanting stick
  have hd1 : T.dir (refCell n b (r + 1) x) ≠ HexDir.W := by
    intro h
    rw [slotOfCell, if_pos h] at hgap
    exact hgap
  have hs1 : T.Slanted (refCell n b (r + 1) x) := T.slanted_of_ne_W hw hd1
  have hbot : T.botCell (refCell n b (r + 1) x) = refCell n b (r + 1) x :=
    T.botCell_eq_self_of_phi_zero hphi1 hs1
  -- the cell directly below it is horizontal, and is the top cell of the band below
  have hdw : T.dir (nbr (refCell n b (r + 1) x) HexDir.SE) = HexDir.W := by
    have h := T.dir_nbr_below_botCell hv (by omega) hw hs1
    rwa [hbot] at h
  have hweq : nbr (refCell n b (r + 1) x) HexDir.SE = walk (refCell n b r x) HexDir.NW (n : ℤ) := by
    refine hex_ext ?_ ?_
    · rw [shearCol_nbr_SE, refCell, shearCol_shearCell, shearCol_walk_NW, refCell,
        shearCol_shearCell]
    · rw [shearRow_nbr_SE, refCell, shearRow_shearCell, shearRow_walk_NW, refCell,
        shearRow_shearCell]
      ring
  obtain ⟨hdirw, -⟩ := T.climb_dir_phi hv hn hw hphi0 n le_rfl
  have hd0 : T.dir (refCell n b r x) = HexDir.W := by
    rw [← hdirw, ← hweq]
    exact hdw
  have hidxw : T.idx (nbr (refCell n b (r + 1) x) HexDir.SE) = T.idx (refCell n b r x) := by
    rw [hweq]
    exact T.climb_idx_W hv hn hw hphi0 hd0 n le_rfl
  -- the cell above the horizontal cell is the gap column
  have habove : nbr (nbr (refCell n b (r + 1) x) HexDir.SE) HexDir.NW = refCell n b (r + 1) x :=
    nbr_nbr_cancel _ (by decide : HexDir.NW = HexDir.SE.opp)
  -- the horizontal cell is not the near end of its stick
  have hi2 : 2 ≤ T.idx (nbr (refCell n b (r + 1) x) HexDir.SE) := by
    by_contra hcon
    have hi1 : T.idx (nbr (refCell n b (r + 1) x) HexDir.SE) = 1 := by
      have := T.idx_pos (nbr (refCell n b (r + 1) x) HexDir.SE)
      omega
    refine T.top_no_slant_head hv (by omega) hdw hi1 ?_
    rw [show HexDir.W + 5 = HexDir.NW from by decide, habove]
    rcases hs1 with h | h
    · exact Or.inr ⟨by rw [h], T.idx_eq_one_of_phi_zero_NW hphi1 h⟩
    · exact Or.inl ⟨by rw [h]; decide, T.idx_eq_length_of_phi_zero_SE hphi1 h⟩
  -- the horizontal cell is at least two cells away from the far end of its stick
  have hin : T.idx (nbr (refCell n b (r + 1) x) HexDir.SE) + 1 ≤ n := by
    by_contra hcon
    have hle := T.idx_le (nbr (refCell n b (r + 1) x) HexDir.SE)
    have hcases : T.idx (nbr (refCell n b (r + 1) x) HexDir.SE) = n ∨
        T.idx (nbr (refCell n b (r + 1) x) HexDir.SE) = n + 1 := by omega
    -- in both cases the cell above is a cell of the horizontal stick filling the space `A`
    obtain ⟨hdA, hcase⟩ := T.dir_backCorner_beyond_tail hv (by omega)
      (T.isLeftLeaningStack_of_dir_W hw hdw) hdw
      (T.sameStack_refl (nbr (refCell n b (r + 1) x) HexDir.SE))
    rcases hcases with hi | hi
    · -- the far end of the stick is the cell just west
      have hlt : T.idx (nbr (refCell n b (r + 1) x) HexDir.SE) < n + 1 := by omega
      have hmem := T.nbr_dir_mem_stickOf (nbr (refCell n b (r + 1) x) HexDir.SE) hlt
      rw [hdw] at hmem
      have hidx' : T.idx (nbr (nbr (refCell n b (r + 1) x) HexDir.SE) HexDir.W) = n + 1 := by
        have h := T.succ_idx (nbr (refCell n b (r + 1) x) HexDir.SE) hlt
        rw [hdw] at h
        omega
      have htail : T.tail (nbr (refCell n b (r + 1) x) HexDir.SE) =
          nbr (nbr (refCell n b (r + 1) x) HexDir.SE) HexDir.W :=
        (T.eq_tail_of_mem_of_idx_eq h0 hmem hidx').symm
      rw [htail, show HexDir.W + 5 = HexDir.NW from by decide] at hdA hcase
      -- the cell east of `A` lies on the same stick, and is the gap column
      have hA1 : 1 < T.idx (nbr (nbr (nbr (refCell n b (r + 1) x) HexDir.SE) HexDir.W)
          HexDir.NW) := by
        rcases hcase with ⟨hiA, -⟩ | ⟨hiA, -⟩
        · omega
        · exact hiA
      have hmemA := T.nbr_dir_opp_mem_stickOf _ hA1
      rw [hdA, show HexDir.W.opp = HexDir.E from by decide] at hmemA
      have hEA : nbr (nbr (nbr (nbr (refCell n b (r + 1) x) HexDir.SE) HexDir.W) HexDir.NW)
          HexDir.E = refCell n b (r + 1) x := by
        rw [nbr_comm, nbr_nbr_cancel _ (by decide : HexDir.E = HexDir.W.opp), habove]
      rw [hEA] at hmemA
      exact hd1 (by rw [T.dir_of_mem_stickOf hmemA, hdA])
    · -- the cell is the far end of its stick, so the cell above it is horizontal
      have htail : T.tail (nbr (refCell n b (r + 1) x) HexDir.SE) =
          nbr (refCell n b (r + 1) x) HexDir.SE := T.tail_eq_self_of_idx_eq hi
      rw [htail, show HexDir.W + 5 = HexDir.NW from by decide, habove] at hdA
      exact hd1 hdA
  refine ⟨n + 1 - T.idx (refCell n b r x), by omega, by omega, ?_⟩
  rw [slotOfCell, if_pos hd0]

/-! ### The tiling is the tiling of the schematic read off it -/

/-- Every cell, translated by the vector `shearCell 0 b`, is reached from the cell at the bottom
of its band in its column by climbing inside the band. -/
lemma cell_add_eq_walk (n : ℕ) (b : ℤ) (c : Hex) :
    c + shearCell 0 b =
      walk (refCell n b (bandRow n (shearRow c)) (shearCol c)) HexDir.NW
        (subRow n (shearRow c)) := by
  have hband := bandRow_mul_add n (shearRow c)
  simp only [shearRow] at hband
  refine hex_ext ?_ ?_
  · rw [shearCol_walk_NW, refCell, shearCol_shearCell]
    simp only [shearCol, shearCell, Prod.fst_add, Prod.snd_add]
    ring
  · rw [shearRow_walk_NW, refCell, shearRow_shearCell]
    simp only [shearRow, shearCell, Prod.snd_add]
    linarith

/-- **The tiling is the tiling described by the schematic read off it**, up to the translation
taking the row `0` to the row `b` at which all the bands start. -/
theorem toTiling_eq_translate (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {b : ℤ} (hb : ∀ c, ((n : ℤ) + 1) ∣ T.bandBase c - b)
    (S : Schematic n) (hS : ∀ r x, S.slot r x = T.slotOfCell (refCell n b r x)) :
    S.toTiling = T.translate (shearCell 0 b) := by
  have key : ∀ c : Hex, S.dirAt c = T.dir (c + shearCell 0 b) ∧
      S.idxAt c = T.idx (c + shearCell 0 b) := by
    intro c
    have h0 := subRow_nonneg n (shearRow c)
    have h1 := subRow_le n (shearRow c)
    obtain ⟨k, hk, hik⟩ : ∃ k : ℕ, k ≤ n ∧ (k : ℤ) = subRow n (shearRow c) :=
      ⟨(subRow n (shearRow c)).toNat, by omega, by omega⟩
    have hcw : c + shearCell 0 b =
        walk (refCell n b (bandRow n (shearRow c)) (shearCol c)) HexDir.NW (k : ℤ) := by
      rw [hik]; exact cell_add_eq_walk n b c
    have hphi : T.phi (refCell n b (bandRow n (shearRow c)) (shearCol c)) = 0 :=
      T.phi_refCell hn hw hb _ _
    have hslotAt : S.slotAt c =
        T.slotOfCell (refCell n b (bandRow n (shearRow c)) (shearCol c)) := hS _ _
    have hsub : S.subOf c = (k : ℤ) := hik.symm
    have hclimb := T.climb_dir_phi hv hn hw hphi k hk
    rcases T.dir_cases hw (refCell n b (bandRow n (shearRow c)) (shearCol c)) with hd | hd | hd
    · -- a column of a block
      have hsl : S.slotAt c =
          .block (n + 1 - T.idx (refCell n b (bandRow n (shearRow c)) (shearCol c))) := by
        rw [hslotAt, slotOfCell, if_pos hd]
      have hpos := T.idx_pos (refCell n b (bandRow n (shearRow c)) (shearCol c))
      have hle := T.idx_le (refCell n b (bandRow n (shearRow c)) (shearCol c))
      refine ⟨?_, ?_⟩
      · rw [S.dirAt_block hsl, hcw, hclimb.1, hd]
      · rw [S.idxAt_block hsl, hcw, T.climb_idx_W hv hn hw hphi hd k hk]
        omega
    · -- a column of the right part of a gap
      have hsl : S.slotAt c = .gapR := by
        rw [hslotAt, slotOfCell, if_neg (by rw [hd]; decide), if_neg (by rw [hd]; decide)]
      refine ⟨?_, ?_⟩
      · rw [S.dirAt_gapR hsl, hcw, hclimb.1, hd]
      · rw [S.idxAt_gapR hsl, hcw, T.climb_idx_NW hv hn hw hphi hd k hk,
          T.idx_eq_one_of_phi_zero_NW hphi hd, hsub]
        omega
    · -- a column of the left part of a gap
      have hsl : S.slotAt c = .gapL := by
        rw [hslotAt, slotOfCell, if_neg (by rw [hd]; decide), if_pos hd]
      refine ⟨?_, ?_⟩
      · rw [S.dirAt_gapL hsl, hcw, hclimb.1, hd]
      · rw [S.idxAt_gapL hsl, hcw, T.climb_idx_SE hv hn hw hphi hd k hk,
          T.idx_eq_length_of_phi_zero_SE hphi hd, hsub]
        omega
  exact StickTiling.ext' (fun c => (key c).1) (fun c => (key c).2)

/-- **Every normalised weave-pattern tiling is described by a block schematic**, up to a
translation. -/
theorem exists_schematic (hv : T.SatisfiesWeaveRules) (hn : 4 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) :
    ∃ (S : Schematic n) (v : Hex), S.toTiling = T.translate v := by
  have hb : ∀ c, ((n : ℤ) + 1) ∣ T.bandBase c - T.bandBase (shearCell 0 0) := by
    intro c
    have h := T.bandBase_congr hv (by omega) hw (shearCell 0 0) c
    push_cast at h
    exact h
  refine ⟨⟨fun r x => T.slotOfCell (refCell n (T.bandBase (shearCell 0 0)) r x),
    fun r x => T.slotOfCell_step hv hn hw hb r x,
    fun r x hgap => T.slotOfCell_overlap hv hn hw hb r x hgap⟩, _,
    T.toTiling_eq_translate hv hn hw hb _ (fun r x => rfl)⟩

end StickTiling

end StickPolyhex
