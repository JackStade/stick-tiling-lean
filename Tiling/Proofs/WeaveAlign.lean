import Tiling.Proofs.WeaveFlanks
import Tiling.Proofs.WeaveSlant

/-!
# The bands of a weave-pattern tiling

Let `T` be a tiling by sticks of length `n ≥ 5` satisfying the weave rules and normalised so
that its horizontal sticks point west (`T.IsWeavePattern HexDir.W`).  In sheared coordinates the
blocks of `T` are `n × n` squares of cells and the left-slanting sticks occupy `n` consecutive
rows of a single column.  This file proves that all these squares and sticks are aligned: there
is a residue class of rows modulo `n` at which every block and every left-slanting stick starts.

The height of a cell inside its block, resp. inside its left-slanting stick, is recorded by
`StickTiling.phi`, a number in `{0, …, n-1}`, and `StickTiling.bandBase c = shearRow c - phi c`
is the row at which the block or the stick of `c` starts.  The main result,
`StickTiling.bandBase_congr`, states that `bandBase` is constant modulo `n`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### The height of a cell inside its block or its slanted stick -/

/-- The height of a cell inside its block (for a horizontal cell, measured by the index of its
flank cell) or inside its left-slanting stick.  It is a number in `{0, …, n-1}`. -/
def phi (c : Hex) : ℤ :=
  if T.dir c = HexDir.W then (T.idx (T.flank HexDir.W c) : ℤ) - 1
  else if T.dir c = HexDir.NW then (T.idx c : ℤ) - 1
  else (n : ℤ) - T.idx c

/-- The row at which the block, resp. the left-slanting stick, of a cell starts. -/
def bandBase (c : Hex) : ℤ := shearRow c - T.phi c

lemma phi_of_dir_W {c : Hex} (h : T.dir c = HexDir.W) :
    T.phi c = (T.idx (T.flank HexDir.W c) : ℤ) - 1 := by rw [phi, if_pos h]

lemma phi_of_dir_NW {c : Hex} (h : T.dir c = HexDir.NW) : T.phi c = (T.idx c : ℤ) - 1 := by
  rw [phi, if_neg (by rw [h]; decide), if_pos h]

lemma phi_of_dir_SE {c : Hex} (h : T.dir c = HexDir.SE) : T.phi c = (n : ℤ) - T.idx c := by
  rw [phi, if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]

/-! ### Basic consequences of the normalisation -/

/-- In a normalised weave pattern every stick is horizontal, or slants left. -/
lemma dir_cases (hw : T.IsWeavePattern HexDir.W) (c : Hex) :
    T.dir c = HexDir.W ∨ T.dir c = HexDir.NW ∨ T.dir c = HexDir.SE := by
  rcases hw.horizontal_or_slantsLeft c with h | h
  · exact Or.inl h
  · rcases h with h | h
    · exact Or.inr (Or.inr (by simpa using h))
    · exact Or.inr (Or.inl (by simpa using h))

lemma slanted_of_ne_W (hw : T.IsWeavePattern HexDir.W) {c : Hex} (h : T.dir c ≠ HexDir.W) :
    T.Slanted c := by
  rcases T.dir_cases hw c with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'
  · exact Or.inr h'

lemma slanted_of_dir_eq {v c : Hex} (hdv : T.dir v = T.dir c) (hs : T.Slanted c) :
    T.Slanted v := by
  rcases hs with h | h
  · exact Or.inl (hdv.trans h)
  · exact Or.inr (hdv.trans h)

lemma dir_ne_W_of_slanted {c : Hex} (hs : T.Slanted c) : T.dir c ≠ HexDir.W := by
  rcases hs with h | h <;> rw [h] <;> decide

lemma isLeftLeaningStack_of_dir_W (hw : T.IsWeavePattern HexDir.W) {c : Hex}
    (h : T.dir c = HexDir.W) : T.IsLeftLeaningStack c := hw.horizontal_leftLeaning c h

/-! ### The height of a cell lies in `{0, …, n-1}` -/

lemma phi_nonneg (hw : T.IsWeavePattern HexDir.W) (c : Hex) : 0 ≤ T.phi c := by
  rcases T.dir_cases hw c with h | h | h
  · rw [T.phi_of_dir_W h]
    have := T.idx_pos (T.flank HexDir.W c)
    omega
  · rw [T.phi_of_dir_NW h]
    have := T.idx_pos c
    omega
  · rw [T.phi_of_dir_SE h]
    have := T.idx_le c
    omega

lemma phi_lt (hw : T.IsWeavePattern HexDir.W) (c : Hex) : T.phi c < n := by
  rcases T.dir_cases hw c with h | h | h
  · rw [T.phi_of_dir_W h]
    have := T.idx_le (T.flank HexDir.W c)
    omega
  · rw [T.phi_of_dir_NW h]
    have := T.idx_le c
    omega
  · rw [T.phi_of_dir_SE h]
    have := T.idx_pos c
    omega

/-- For a left-slanting cell the height inside the band is the number of rows above the lowest
cell of its stick. -/
lemma phi_eq_sub_botCell (hn : 5 ≤ n) {c : Hex} (hs : T.Slanted c) :
    T.phi c = shearRow c - shearRow (T.botCell c) := by
  rcases hs with h | h
  · rw [T.phi_of_dir_NW h, T.botCell_of_NW h, (T.shear_head_NW h).2]
    ring
  · rw [T.phi_of_dir_SE h, T.botCell_of_SE h, shear_tail_of_head T (by omega : 0 < n),
      h, shearRow_walk_SE, (T.shear_head_SE h).2]
    have := T.idx_le c
    omega

/-! ### Reading off the position of a cell inside its stick -/

/-- All the cells of a left-slanting stick lie in the same column. -/
lemma shearCol_of_mem_stickOf_slanted {z x : Hex} (hs : T.Slanted z) (hx : x ∈ T.stickOf z) :
    shearCol x = shearCol z := by
  rw [T.mem_stickOf_iff] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rcases hs with h | h
  · rw [cellOfStick, h, shearCol_walk_NW, (T.shear_head_NW h).1]
  · rw [cellOfStick, h, shearCol_walk_SE, (T.shear_head_SE h).1]

/-- A horizontal cell whose western neighbour is not horizontal is the far end of its stick. -/
lemma idx_eq_n_of_nbr_W_ne {p : Hex} (hd : T.dir p = HexDir.W)
    (h : T.dir (nbr p HexDir.W) ≠ HexDir.W) : T.idx p = n := by
  by_contra hne
  have hlt : T.idx p < n := lt_of_le_of_ne (T.idx_le p) hne
  have hstep := T.succ_dir p hlt
  rw [hd] at hstep
  exact h hstep

/-- A horizontal cell whose eastern neighbour is not horizontal is the near end of its stick. -/
lemma idx_eq_one_of_nbr_E_ne {p : Hex} (hd : T.dir p = HexDir.W)
    (h : T.dir (nbr p HexDir.E) ≠ HexDir.W) : T.idx p = 1 := by
  by_contra hne
  have hgt : 1 < T.idx p := lt_of_le_of_ne (T.idx_pos p) (Ne.symm hne)
  have hstep := T.pred_dir p hgt
  rw [hd, show HexDir.W.opp = HexDir.E from by decide] at hstep
  exact h hstep

/-- The flank cell of a horizontal cell whose western neighbour is not horizontal is that
neighbour. -/
lemma flank_eq_nbr_W {p : Hex} (hd : T.dir p = HexDir.W)
    (h : T.dir (nbr p HexDir.W) ≠ HexDir.W) : T.flank HexDir.W p = nbr p HexDir.W := by
  rw [flank, T.tail_eq_self_of_idx_eq (T.idx_eq_n_of_nbr_W_ne hd h)]

/-- The front flank cell of a horizontal cell whose eastern neighbour is not horizontal is that
neighbour. -/
lemma frontFlank_eq_nbr_E {p : Hex} (hd : T.dir p = HexDir.W)
    (h : T.dir (nbr p HexDir.E) ≠ HexDir.W) : T.frontFlank HexDir.W p = nbr p HexDir.E := by
  rw [frontFlank, show HexDir.W.opp = HexDir.E from by decide,
    T.head_eq_self_of_idx_eq (T.idx_eq_one_of_nbr_E_ne hd h)]

/-- A horizontal cell whose upper neighbour is not horizontal lies on the topmost stick of its
block. -/
lemma flank_idx_eq_n_of_above_ne (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {p : Hex} (hd : T.dir p = HexDir.W)
    (h : T.dir (nbr p HexDir.NW) ≠ HexDir.W) : T.idx (T.flank HexDir.W p) = n := by
  by_contra hne
  have hlt : T.idx (T.flank HexDir.W p) < n := lt_of_le_of_ne (T.idx_le _) hne
  obtain ⟨hd', -⟩ := T.block_up hv (by omega) (T.isLeftLeaningStack_of_dir_W hw hd) hd hlt
  rw [show HexDir.W + 5 = HexDir.NW from by decide] at hd'
  exact h hd'

/-- A horizontal cell whose lower neighbour is not horizontal lies on the bottommost stick of its
block. -/
lemma flank_idx_eq_one_of_below_ne (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {p : Hex} (hd : T.dir p = HexDir.W)
    (h : T.dir (nbr p HexDir.SE) ≠ HexDir.W) : T.idx (T.flank HexDir.W p) = 1 := by
  by_contra hne
  have hgt : 1 < T.idx (T.flank HexDir.W p) := lt_of_le_of_ne (T.idx_pos _) (Ne.symm hne)
  obtain ⟨hd', -⟩ := T.block_down hv (by omega) (T.isLeftLeaningStack_of_dir_W hw hd) hd hgt
  rw [show HexDir.W + 2 = HexDir.SE from by decide] at hd'
  exact h hd'

/-- The cell of a left-slanting stick lying `k` rows above its lowest cell. -/
lemma exists_cell_of_slanted (hn : 5 ≤ n) {c : Hex} (hs : T.Slanted c) {k : ℤ} (hk0 : 0 ≤ k)
    (hkn : k < n) :
    ∃ w, T.dir w = T.dir c ∧ T.botCell w = T.botCell c ∧
      shearRow w = shearRow (T.botCell c) + k ∧ shearCol w = shearCol c := by
  have h0n : 0 < n := by omega
  refine ⟨walk (T.botCell c) HexDir.NW k, ?_, ?_, ?_, ?_⟩
  · have hmem : walk (T.botCell c) HexDir.NW k ∈ T.stickOf c := by
      rw [T.stickOf_eq_image_botCell h0n hs]
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨k.toNat, by omega, by rw [Int.toNat_of_nonneg hk0]⟩
    exact T.dir_of_mem_stickOf hmem
  · have hmem : walk (T.botCell c) HexDir.NW k ∈ T.stickOf c := by
      rw [T.stickOf_eq_image_botCell h0n hs]
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨k.toNat, by omega, by rw [Int.toNat_of_nonneg hk0]⟩
    exact T.botCell_congr (T.stickOf_eq_of_mem hmem)
  · rw [shearRow_walk_NW]
  · rw [shearCol_walk_NW]
    exact T.shearCol_of_mem_stickOf_slanted hs (T.botCell_mem_stickOf h0n c)

/-! ### Adjacent left-slanting sticks are aligned -/

private lemma botRow_le_east (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {c : Hex} (hs : T.Slanted c)
    (hs' : T.Slanted (nbr c HexDir.E)) :
    shearRow (T.botCell (nbr c HexDir.E)) ≤ shearRow (T.botCell c) := by
  by_contra hcon
  push_neg at hcon
  have h0n : 0 < n := by omega
  have hrow' : shearRow (nbr c HexDir.E) = shearRow c := by
    simp [shearRow, nbr, HexDir.vec, HexDir.E]
  have hcol' : shearCol (nbr c HexDir.E) = shearCol c + 1 := by
    simp [shearCol, nbr, HexDir.vec, HexDir.E]; ring
  have hphi := T.phi_eq_sub_botCell hn hs
  have hphi' := T.phi_eq_sub_botCell hn hs'
  have hb0 := T.phi_nonneg hw c
  have hbn := T.phi_lt hw c
  have hb0' := T.phi_nonneg hw (nbr c HexDir.E)
  have hbn' := T.phi_lt hw (nbr c HexDir.E)
  obtain ⟨v, hdv, hbv, hrv, hcv⟩ :=
    T.exists_cell_of_slanted hn hs
      (k := shearRow (T.botCell (nbr c HexDir.E)) - 1 - shearRow (T.botCell c))
      (by omega) (by omega)
  have hsv : T.Slanted v := T.slanted_of_dir_eq hdv hs
  -- the cell just east of `v` is the cell just below the lowest cell of the eastern stick
  have hp : nbr v HexDir.E = nbr (T.botCell (nbr c HexDir.E)) HexDir.SE := by
    refine hex_ext ?_ ?_
    · rw [show shearCol (nbr v HexDir.E) = shearCol v + 1 from by
          simp [shearCol, nbr, HexDir.vec, HexDir.E]; ring,
        show shearCol (nbr (T.botCell (nbr c HexDir.E)) HexDir.SE)
            = shearCol (T.botCell (nbr c HexDir.E)) from by
          simp [shearCol, nbr, HexDir.vec, HexDir.SE]; ring,
        T.shearCol_of_mem_stickOf_slanted hs' (T.botCell_mem_stickOf h0n _), hcv, hcol']
    · rw [show shearRow (nbr v HexDir.E) = shearRow v from by
          simp [shearRow, nbr, HexDir.vec, HexDir.E],
        show shearRow (nbr (T.botCell (nbr c HexDir.E)) HexDir.SE)
            = shearRow (T.botCell (nbr c HexDir.E)) - 1 from by
          simp [shearRow, nbr, HexDir.vec, HexDir.SE]; ring, hrv]
      omega
  have hdp : T.dir (nbr v HexDir.E) = HexDir.W := by
    rw [hp]
    exact T.dir_nbr_below_botCell hv hn hw hs'
  have hvp : nbr (nbr v HexDir.E) HexDir.W = v :=
    nbr_nbr_cancel v (by decide : HexDir.W = HexDir.E.opp)
  have hflank : T.flank HexDir.W (nbr v HexDir.E) = v := by
    rw [T.flank_eq_nbr_W hdp (by rw [hvp]; exact T.dir_ne_W_of_slanted hsv), hvp]
  have habove : nbr (nbr v HexDir.E) HexDir.NW = T.botCell (nbr c HexDir.E) := by
    rw [hp]
    exact nbr_nbr_cancel _ (by decide : HexDir.NW = HexDir.SE.opp)
  have hdabove : T.dir (nbr (nbr v HexDir.E) HexDir.NW) ≠ HexDir.W := by
    rw [habove]
    exact T.dir_ne_W_of_slanted
      (T.slanted_of_dir_eq (T.dir_botCell h0n (nbr c HexDir.E)) hs')
  have hidxv : T.idx v = n := by
    rw [← hflank]
    exact T.flank_idx_eq_n_of_above_ne hv hn hw hdp hdabove
  have hdvNW : T.dir v = HexDir.NW := by
    rw [← hflank]
    have := T.dir_flank_eq hv (by omega)
      (T.isLeftLeaningStack_of_dir_W hw hdp) hdp
    simpa using this
  have hphiv : T.phi v = shearRow v - shearRow (T.botCell c) := by
    rw [T.phi_eq_sub_botCell hn (Or.inl hdvNW), hbv]
  rw [T.phi_of_dir_NW hdvNW, hidxv] at hphiv
  omega

private lemma botRow_ge_east (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {c : Hex} (hs : T.Slanted c)
    (hs' : T.Slanted (nbr c HexDir.E)) :
    shearRow (T.botCell c) ≤ shearRow (T.botCell (nbr c HexDir.E)) := by
  by_contra hcon
  push_neg at hcon
  have h0n : 0 < n := by omega
  have hrow' : shearRow (nbr c HexDir.E) = shearRow c := by
    simp [shearRow, nbr, HexDir.vec, HexDir.E]
  have hcol' : shearCol (nbr c HexDir.E) = shearCol c + 1 := by
    simp [shearCol, nbr, HexDir.vec, HexDir.E]; ring
  have hphi := T.phi_eq_sub_botCell hn hs
  have hphi' := T.phi_eq_sub_botCell hn hs'
  have hb0 := T.phi_nonneg hw c
  have hbn := T.phi_lt hw c
  have hb0' := T.phi_nonneg hw (nbr c HexDir.E)
  have hbn' := T.phi_lt hw (nbr c HexDir.E)
  obtain ⟨q, hdq, hbq, hrq, hcq⟩ :=
    T.exists_cell_of_slanted hn hs'
      (k := shearRow (T.botCell c) - 1 - shearRow (T.botCell (nbr c HexDir.E)))
      (by omega) (by omega)
  have hsq : T.Slanted q := T.slanted_of_dir_eq hdq hs'
  have hdp : T.dir (nbr (T.botCell c) HexDir.SE) = HexDir.W :=
    T.dir_nbr_below_botCell hv hn hw hs
  have hq : nbr (nbr (T.botCell c) HexDir.SE) HexDir.E = q := by
    refine hex_ext ?_ ?_
    · rw [show shearCol (nbr (nbr (T.botCell c) HexDir.SE) HexDir.E)
            = shearCol (nbr (T.botCell c) HexDir.SE) + 1 from by
          simp [shearCol, nbr, HexDir.vec, HexDir.E]; ring,
        show shearCol (nbr (T.botCell c) HexDir.SE) = shearCol (T.botCell c) from by
          simp [shearCol, nbr, HexDir.vec, HexDir.SE]; ring,
        T.shearCol_of_mem_stickOf_slanted hs (T.botCell_mem_stickOf h0n c), hcq, hcol']
    · rw [show shearRow (nbr (nbr (T.botCell c) HexDir.SE) HexDir.E)
            = shearRow (nbr (T.botCell c) HexDir.SE) from by
          simp [shearRow, nbr, HexDir.vec, HexDir.E],
        show shearRow (nbr (T.botCell c) HexDir.SE) = shearRow (T.botCell c) - 1 from by
          simp [shearRow, nbr, HexDir.vec, HexDir.SE]; ring, hrq]
      omega
  have hdqne : T.dir (nbr (nbr (T.botCell c) HexDir.SE) HexDir.E) ≠ HexDir.W := by
    rw [hq]
    exact T.dir_ne_W_of_slanted hsq
  have hfront : T.frontFlank HexDir.W (nbr (T.botCell c) HexDir.SE) = q := by
    rw [T.frontFlank_eq_nbr_E hdp hdqne, hq]
  have habove : nbr (nbr (T.botCell c) HexDir.SE) HexDir.NW = T.botCell c :=
    nbr_nbr_cancel _ (by decide : HexDir.NW = HexDir.SE.opp)
  have hdabove : T.dir (nbr (nbr (T.botCell c) HexDir.SE) HexDir.NW) ≠ HexDir.W := by
    rw [habove]
    exact T.dir_ne_W_of_slanted (T.slanted_of_dir_eq (T.dir_botCell h0n c) hs)
  have hidxflank : T.idx (T.flank HexDir.W (nbr (T.botCell c) HexDir.SE)) = n :=
    T.flank_idx_eq_n_of_above_ne hv hn hw hdp hdabove
  have hsum := T.flank_idx_add hv hn hw hdp
  rw [hidxflank, hfront] at hsum
  have hdqSE : T.dir q = HexDir.SE := by
    rw [← hfront]
    have := T.dir_frontFlank hv (by omega)
      (T.isLeftLeaningStack_of_dir_W hw hdp) hdp
    simpa using this
  have hphiq : T.phi q = shearRow q - shearRow (T.botCell (nbr c HexDir.E)) := by
    rw [T.phi_eq_sub_botCell hn (Or.inr hdqSE), hbq]
  rw [T.phi_of_dir_SE hdqSE] at hphiq
  omega

/-- **Two left-slanting sticks in neighbouring columns occupy the same rows.** -/
theorem botCell_east (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    {c : Hex} (hs : T.Slanted c) (hs' : T.Slanted (nbr c HexDir.E)) :
    shearRow (T.botCell (nbr c HexDir.E)) = shearRow (T.botCell c) :=
  le_antisymm (T.botRow_le_east hv hn hw hs hs') (T.botRow_ge_east hv hn hw hs hs')

/-! ### The two steps -/

/-- **The height of a cell inside its band does not change from one column to the next.** -/
theorem phi_east (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    (c : Hex) : T.phi (nbr c HexDir.E) = T.phi c := by
  have h0n : 0 < n := by omega
  have hrow : shearRow (nbr c HexDir.E) = shearRow c := by
    simp [shearRow, nbr, HexDir.vec, HexDir.E]
  by_cases hd : T.dir c = HexDir.W
  · by_cases hi : T.idx c = 1
    · -- `c` is the near end of its stick: its eastern neighbour is the front flank cell
      have hhead : T.head c = c := T.head_eq_self_of_idx_eq hi
      have hfront : T.frontFlank HexDir.W c = nbr c HexDir.E := by
        rw [frontFlank, show HexDir.W.opp = HexDir.E from by decide, hhead]
      have hdE : T.dir (nbr c HexDir.E) = HexDir.SE := by
        rw [← hfront]
        have := T.dir_frontFlank hv (by omega) (T.isLeftLeaningStack_of_dir_W hw hd) hd
        simpa using this
      have hsum := T.flank_idx_add hv hn hw hd
      rw [hfront] at hsum
      rw [T.phi_of_dir_SE hdE, T.phi_of_dir_W hd]
      omega
    · -- `c` is not the near end: its eastern neighbour lies on the same stick
      have hgt : 1 < T.idx c := lt_of_le_of_ne (T.idx_pos c) (Ne.symm hi)
      have hmem : nbr c (T.dir c).opp ∈ T.stickOf c := T.nbr_dir_opp_mem_stickOf c hgt
      rw [hd, show HexDir.W.opp = HexDir.E from by decide] at hmem
      have hdE : T.dir (nbr c HexDir.E) = HexDir.W := by rw [T.dir_of_mem_stickOf hmem, hd]
      have hflank : T.flank HexDir.W (nbr c HexDir.E) = T.flank HexDir.W c :=
        T.flank_congr (T.stickOf_eq_of_mem hmem)
      rw [T.phi_of_dir_W hdE, T.phi_of_dir_W hd, hflank]
  · -- `c` is left-slanting
    have hs : T.Slanted c := T.slanted_of_ne_W hw hd
    by_cases hd' : T.dir (nbr c HexDir.E) = HexDir.W
    · -- the eastern neighbour is horizontal: it is the far end of its stick, with flank `c`
      have hback : nbr (nbr c HexDir.E) HexDir.W = c :=
        nbr_nbr_cancel c (by decide : HexDir.W = HexDir.E.opp)
      have hne : T.dir (nbr (nbr c HexDir.E) HexDir.W) ≠ HexDir.W := by
        rw [hback]; exact T.dir_ne_W_of_slanted hs
      have hflank : T.flank HexDir.W (nbr c HexDir.E) = c := by
        rw [T.flank_eq_nbr_W hd' hne, hback]
      have hdNW : T.dir c = HexDir.NW := by
        rw [← hflank] at hs ⊢
        have := T.dir_flank_eq hv (by omega) (T.isLeftLeaningStack_of_dir_W hw hd') hd'
        simpa using this
      rw [T.phi_of_dir_W hd', hflank, T.phi_of_dir_NW hdNW]
    · -- both cells are left-slanting: their sticks occupy the same rows
      have hs' : T.Slanted (nbr c HexDir.E) := T.slanted_of_ne_W hw hd'
      rw [T.phi_eq_sub_botCell hn hs, T.phi_eq_sub_botCell hn hs',
        T.botCell_east hv hn hw hs hs', hrow]

/-- **Going up one row either increases the height inside the band by one, or starts a new
band.** -/
theorem phi_up (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    (c : Hex) :
    (T.phi c + 1 < n ∧ T.phi (nbr c HexDir.NW) = T.phi c + 1) ∨
      (T.phi c + 1 = n ∧ T.phi (nbr c HexDir.NW) = 0) := by
  have h0n : 0 < n := by omega
  have hbelow : nbr (nbr c HexDir.NW) HexDir.SE = c :=
    nbr_nbr_cancel c (by decide : HexDir.SE = HexDir.NW.opp)
  -- the cell above a cell whose band is full starts a new band
  have hnew : T.phi c + 1 = n → T.dir c ≠ HexDir.W ∨ T.idx (T.flank HexDir.W c) = n →
      T.phi (nbr c HexDir.NW) = 0 := by
    intro hfull htop
    by_cases hd' : T.dir (nbr c HexDir.NW) = HexDir.W
    · -- the cell above is horizontal: it lies at the bottom of its own block
      have hidx : T.idx (T.flank HexDir.W (nbr c HexDir.NW)) = 1 := by
        rcases htop with hne | hfull
        · refine T.flank_idx_eq_one_of_below_ne hv hn hw hd' ?_
          rw [hbelow]; exact hne
        · have := T.flank_idx_eq_one_of_top hv (by omega) (u := HexDir.W)
            (c := c) (by rw [hfull]) (by simpa using hd')
            (by simpa using T.isLeftLeaningStack_of_dir_W hw (by simpa using hd'))
          simpa using this
      rw [T.phi_of_dir_W hd', hidx]
      norm_num
    · -- the cell above is left-slanting: it is the lowest cell of its stick
      have hs' : T.Slanted (nbr c HexDir.NW) := T.slanted_of_ne_W hw hd'
      have hbot : T.botCell (nbr c HexDir.NW) = nbr c HexDir.NW := by
        by_contra hne
        -- otherwise the cell below would belong to the same left-slanting stick
        have hmem : nbr (nbr c HexDir.NW) HexDir.SE ∈ T.stickOf (nbr c HexDir.NW) := by
          rcases hs' with h | h
          · have hgt : 1 < T.idx (nbr c HexDir.NW) := by
              rcases Nat.lt_or_ge 1 (T.idx (nbr c HexDir.NW)) with h' | h'
              · exact h'
              · exact absurd (by
                  rw [T.botCell_of_NW h,
                    T.head_eq_self_of_idx_eq (by have := T.idx_pos (nbr c HexDir.NW); omega)])
                  hne
            have := T.nbr_dir_opp_mem_stickOf (nbr c HexDir.NW) hgt
            rwa [h, show HexDir.NW.opp = HexDir.SE from by decide] at this
          · have hlt : T.idx (nbr c HexDir.NW) < n := by
              rcases Nat.lt_or_ge (T.idx (nbr c HexDir.NW)) n with h' | h'
              · exact h'
              · exact absurd (by
                  rw [T.botCell_of_SE h,
                    T.tail_eq_self_of_idx_eq (by have := T.idx_le (nbr c HexDir.NW); omega)])
                  hne
            have := T.nbr_dir_mem_stickOf (nbr c HexDir.NW) hlt
            rwa [h] at this
        rw [hbelow] at hmem
        have hdc : T.dir c = T.dir (nbr c HexDir.NW) := T.dir_of_mem_stickOf hmem
        -- but `c` is the cell below, which is a cell of a different stick
        have hbc : T.botCell c = T.botCell (nbr c HexDir.NW) :=
          T.botCell_congr (T.stickOf_eq_of_mem hmem)
        have hphi_c := T.phi_eq_sub_botCell hn (T.slanted_of_dir_eq hdc hs')
        have hphi_c' := T.phi_eq_sub_botCell hn hs'
        have hrow : shearRow (nbr c HexDir.NW) = shearRow c + 1 := by
          simp [shearRow, nbr, HexDir.vec, HexDir.NW]
        have hlt := T.phi_lt hw (nbr c HexDir.NW)
        -- the two cells of one stick differ by one row, so `phi` differs by one; but `phi c`
        -- is already maximal
        rw [hbc] at hphi_c
        omega
      rw [T.phi_eq_sub_botCell hn hs', hbot]
      ring
  by_cases hd : T.dir c = HexDir.W
  · -- horizontal cells
    have hL := T.isLeftLeaningStack_of_dir_W hw hd
    by_cases hfull : T.idx (T.flank HexDir.W c) = n
    · right
      refine ⟨by rw [T.phi_of_dir_W hd, hfull]; omega, ?_⟩
      exact hnew (by rw [T.phi_of_dir_W hd, hfull]; omega) (Or.inr hfull)
    · left
      have hlt : T.idx (T.flank HexDir.W c) < n := lt_of_le_of_ne (T.idx_le _) hfull
      obtain ⟨hd', -, -, -, hfi⟩ := T.block_up hv (by omega) hL hd hlt
      rw [show HexDir.W + 5 = HexDir.NW from by decide] at hd' hfi
      refine ⟨by rw [T.phi_of_dir_W hd]; omega, ?_⟩
      rw [T.phi_of_dir_W hd', T.phi_of_dir_W hd, hfi]
      push_cast
      ring
  · -- left-slanting cells
    have hs : T.Slanted c := T.slanted_of_ne_W hw hd
    by_cases htop : T.phi c + 1 = n
    · exact Or.inr ⟨htop, hnew htop (Or.inl hd)⟩
    · left
      have hphi := T.phi_eq_sub_botCell hn hs
      have hlt := T.phi_lt hw c
      have hge := T.phi_nonneg hw c
      -- the cell above lies on the same stick
      have hmem : nbr c HexDir.NW ∈ T.stickOf c := by
        rcases hs with h | h
        · have hlt' : T.idx c < n := by
            rw [T.phi_of_dir_NW h] at hlt htop
            omega
          have := T.nbr_dir_mem_stickOf c hlt'
          rwa [h] at this
        · have hgt : 1 < T.idx c := by
            rw [T.phi_of_dir_SE h] at htop hlt
            have := T.idx_le c
            omega
          have := T.nbr_dir_opp_mem_stickOf c hgt
          rwa [h, show HexDir.SE.opp = HexDir.NW from by decide] at this
      have hdir : T.dir (nbr c HexDir.NW) = T.dir c := T.dir_of_mem_stickOf hmem
      have hbot : T.botCell (nbr c HexDir.NW) = T.botCell c :=
        T.botCell_congr (T.stickOf_eq_of_mem hmem)
      have hrow : shearRow (nbr c HexDir.NW) = shearRow c + 1 := by
        simp [shearRow, nbr, HexDir.vec, HexDir.NW]
      have hphi' := T.phi_eq_sub_botCell hn (T.slanted_of_dir_eq hdir hs)
      rw [hbot, hrow] at hphi'
      exact ⟨by omega, by omega⟩

/-- **Going up one row inside a band.**  If the cell `c` is not at the top of its band, the cell
directly above it lies on the same block or on the same left-slanting stick: it is covered in the
same direction, its height inside the band is one larger, and its index is the expected one. -/
theorem data_up (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    (c : Hex) (hlt : T.phi c + 1 < n) :
    T.dir (nbr c HexDir.NW) = T.dir c ∧ T.phi (nbr c HexDir.NW) = T.phi c + 1 ∧
      T.idx (nbr c HexDir.NW) =
        (if T.dir c = HexDir.W then T.idx c
          else if T.dir c = HexDir.NW then T.idx c + 1 else T.idx c - 1) := by
  have h0n : 0 < n := by omega
  rcases T.dir_cases hw c with hd | hd | hd
  · -- horizontal
    have hphi := T.phi_of_dir_W hd
    have hfl : T.idx (T.flank HexDir.W c) < n := by omega
    obtain ⟨hd', hi', -, -, hfi⟩ :=
      T.block_up hv (by omega) (T.isLeftLeaningStack_of_dir_W hw hd) hd hfl
    rw [show HexDir.W + 5 = HexDir.NW from by decide] at hd' hi' hfi
    refine ⟨by rw [hd', hd], ?_, by rw [hi', if_pos hd]⟩
    rw [T.phi_of_dir_W hd', hfi, hphi]
    push_cast
    ring
  · -- pointing north-west
    have hphi := T.phi_of_dir_NW hd
    have hidx : T.idx c < n := by omega
    have hmem := T.nbr_dir_mem_stickOf c hidx
    rw [hd] at hmem
    have hd' : T.dir (nbr c HexDir.NW) = HexDir.NW := by rw [T.dir_of_mem_stickOf hmem, hd]
    have hi' : T.idx (nbr c HexDir.NW) = T.idx c + 1 := by
      have := T.succ_idx c hidx
      rwa [hd] at this
    refine ⟨by rw [hd', hd], ?_, by rw [hi', if_neg (by rw [hd]; decide), if_pos hd]⟩
    rw [T.phi_of_dir_NW hd', hi', hphi]
    push_cast
    ring
  · -- pointing south-east
    have hphi := T.phi_of_dir_SE hd
    have hle := T.idx_le c
    have hidx : 1 < T.idx c := by omega
    have hmem := T.nbr_dir_opp_mem_stickOf c hidx
    rw [hd, show HexDir.SE.opp = HexDir.NW from by decide] at hmem
    have hd' : T.dir (nbr c HexDir.NW) = HexDir.SE := by rw [T.dir_of_mem_stickOf hmem, hd]
    have hi' : T.idx (nbr c HexDir.NW) = T.idx c - 1 := by
      have := T.pred_idx c hidx
      rwa [hd, show HexDir.SE.opp = HexDir.NW from by decide] at this
    refine ⟨by rw [hd', hd], ?_, by
      rw [hi', if_neg (by rw [hd]; decide), if_neg (by rw [hd]; decide)]⟩
    rw [T.phi_of_dir_SE hd', hi', hphi]
    have := T.idx_pos c
    omega

/-! ### The base of the band is constant modulo `n` -/

theorem bandBase_east (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    (c : Hex) : T.bandBase (nbr c HexDir.E) = T.bandBase c := by
  have h := T.phi_east hv hn hw c
  have hrow : shearRow (nbr c HexDir.E) = shearRow c := by
    simp [shearRow, nbr, HexDir.vec, HexDir.E]
  simp only [bandBase, h, hrow]

theorem bandBase_up (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    (c : Hex) :
    T.bandBase (nbr c HexDir.NW) = T.bandBase c ∨
      T.bandBase (nbr c HexDir.NW) = T.bandBase c + n := by
  have hrow : shearRow (nbr c HexDir.NW) = shearRow c + 1 := by
    simp [shearRow, nbr, HexDir.vec, HexDir.NW]
  rcases T.phi_up hv hn hw c with ⟨-, h⟩ | ⟨h1, h2⟩
  · left; simp only [bandBase, h, hrow]; ring
  · right; simp only [bandBase, h2, hrow]; omega

/-- Passing to a neighbouring cell changes the base of the band by a multiple of `n`. -/
lemma bandBase_nbr (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    (c : Hex) (e : HexDir) : (n : ℤ) ∣ T.bandBase (nbr c e) - T.bandBase c := by
  have hE : ∀ z : Hex, T.bandBase (nbr z HexDir.E) = T.bandBase z := T.bandBase_east hv hn hw
  have hNW : ∀ z : Hex, (n : ℤ) ∣ T.bandBase (nbr z HexDir.NW) - T.bandBase z := by
    intro z
    rcases T.bandBase_up hv hn hw z with h | h <;> rw [h] <;> simp
  have hW : ∀ z : Hex, T.bandBase (nbr z HexDir.W) = T.bandBase z := by
    intro z
    have h := hE (nbr z HexDir.W)
    rw [nbr_nbr_cancel z (by decide : HexDir.E = HexDir.W.opp)] at h
    exact h.symm
  have hSE : ∀ z : Hex, (n : ℤ) ∣ T.bandBase (nbr z HexDir.SE) - T.bandBase z := by
    intro z
    have h := hNW (nbr z HexDir.SE)
    rw [nbr_nbr_cancel z (by decide : HexDir.NW = HexDir.SE.opp)] at h
    exact dvd_sub_comm.mp h
  rcases HexDir.cases_six e with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hE c]; simp
  · rw [show nbr c HexDir.NE = nbr (nbr c HexDir.E) HexDir.NW from
      (nbr_nbr_of_vec c (by decide : HexDir.E.vec + HexDir.NW.vec = HexDir.NE.vec)).symm]
    have := hNW (nbr c HexDir.E)
    rwa [hE c] at this
  · exact hNW c
  · rw [hW c]; simp
  · rw [show nbr c HexDir.SW = nbr (nbr c HexDir.W) HexDir.SE from
      (nbr_nbr_of_vec c (by decide : HexDir.W.vec + HexDir.SE.vec = HexDir.SW.vec)).symm]
    have := hSE (nbr c HexDir.W)
    rwa [hW c] at this
  · exact hSE c

/-- **The bands of the tiling are aligned**: the row at which the block or the left-slanting
stick of a cell starts is the same for all cells, modulo `n`. -/
theorem bandBase_congr (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) (hw : T.IsWeavePattern HexDir.W)
    (c c' : Hex) : (n : ℤ) ∣ T.bandBase c' - T.bandBase c := by
  refine forall_of_nbr_closed (P := fun z => (n : ℤ) ∣ T.bandBase z - T.bandBase c)
    (z₀ := c) (by simp) (fun z hz e => ?_) c'
  have h := T.bandBase_nbr hv hn hw z e
  have hsum := dvd_add h hz
  simpa [sub_add_sub_cancel] using hsum

end StickTiling

end StickPolyhex
