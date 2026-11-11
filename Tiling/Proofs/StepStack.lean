import Tiling.Proofs.HoleEnds

/-!
# The neighbours of a horizontal stack are anchored

This file proves the first of the two propagation steps of the covering argument: every cell
adjacent to a cell of a left-leaning stack of horizontal sticks of direction `u` is anchored,
i.e. lies on a horizontal stick of direction `u` in a left-leaning stack, or on a left-slanting
stick resting on such a stack from above or from below.

By `StickTiling.nbr_classification` such a neighbour lies in the stack itself, on one of the two
sticks flanking the stack, in the row above the topmost stick (or the corner cell beyond its
near end), or in the row below the bottommost stick; each of these possibilities is treated in
turn, using the descriptions of the two rows provided by `StickTiling.top_row_structure` and
`StickTiling.bot_row_ascend`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- **The neighbours of a horizontal stack are anchored.** -/
theorem anchored_nbr_of_leftLeaning (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {c p : Hex}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hp : T.SameStack c p) (e : HexDir) :
    T.Anchored u (nbr p e) := by
  have h0n : 0 < n := by omega
  -- ### the topmost stick `x` and the row above it
  obtain ⟨x, hx, hnex⟩ := T.exists_backCorner_not_sameStack hv (by omega) hL hu
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have htop := T.tail_nbr_eq_tail_flank hv (by omega) hL hu hx hnex
  obtain ⟨hdA, hcaseA⟩ := T.dir_backCorner_beyond_tail hv (by omega) hL hu hx
  obtain ⟨hi1, hin⟩ :
      1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n := by
    rcases hcaseA with ⟨-, hsame⟩ | hcaseA
    · exact absurd hsame hnex
    · exact hcaseA
  have hLA : T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)) := by
    rcases T.isLeftLeaningStack_backCorner hv (by omega) hL hu hx with h | h
    · exact absurd h hnex
    · exact h
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ :=
    T.top_row_structure hv (by omega) hL hu hx hi1 hin
  have hLs : T.IsLeftLeaningStack (T.upCell u x s) :=
    T.isLeftLeaningStack_upCell hv (by omega) hds his hd5 hi5
  -- ### the bottommost stick `y` and the row below it
  obtain ⟨y, hy, hney⟩ := T.exists_frontCorner_not_sameStack hv (by omega) hL hu
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hy, hu]
  have hbot := T.tail_nbr_eq_head_flank hv (by omega) hL hu hy hney
  obtain ⟨hdC, hcaseC⟩ := T.dir_frontCorner_beyond_head hv (by omega) hL hu hy
  rw [← T.downCell_zero u y] at hdC hney hcaseC
  obtain ⟨hi1', hin'⟩ : 1 < T.idx (T.downCell u y 0) ∧ T.idx (T.downCell u y 0) < n := by
    rcases hcaseC with ⟨-, hsame⟩ | hcaseC
    · exact absurd hsame hney
    · exact hcaseC
  have hLC : T.IsLeftLeaningStack (T.downCell u y 0) := by
    rcases T.isLeftLeaningStack_frontCorner hv (by omega) hL hu hy with h | h
    · rw [← T.downCell_zero u y] at h
      exact absurd h hney
    · rw [← T.downCell_zero u y] at h
      exact h
  obtain ⟨hdt, hit⟩ := T.downCell_tail_of_frontCorner hdC
  obtain ⟨w, hwt, hwn, hdw, hiw, hd2, hi2, hrun⟩ := T.bot_row_ascend hv (by omega) hdy
    (t := n - T.idx (T.downCell u y 0)) (by omega) (by omega) ⟨hdt, hit⟩
  have hLw : T.IsLeftLeaningStack (T.downCell u y w) :=
    T.isLeftLeaningStack_downCell hv (by omega) (by omega) hdw hiw hd2 hi2
  -- ### the cells of the row above the topmost stick are anchored
  have hup : ∀ j, j < n → T.Anchored u (T.upCell u x j) := by
    intro j hj
    by_cases hjs : j ≤ s
    · have hmem := T.upCell_mem_stickOf_of_le hds his (by omega) hjs
      exact Or.inl ⟨by rw [T.dir_of_mem_stickOf hmem, hds],
        T.isLeftLeaningStack_of_sameStack hLs (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))⟩
    · push_neg at hjs
      rcases hrow j hjs hj with hsl | hmem
      · refine Or.inr (Or.inl ⟨walk (T.head x) u (j : ℤ), (T.dir_idx_rowBase hdx hj).1, ?_,
          hsl, T.self_mem_stickOf _⟩)
        have hmemx : walk (T.head x) u (j : ℤ) ∈ T.stickOf x := by
          rw [T.mem_stickOf_iff]
          exact ⟨j, hj, by rw [cellOfStick, hdx]⟩
        exact T.isLeftLeaningStack_of_sameStack hL
          (SameStack.trans T hx (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem hmemx).symm))
      · exact Or.inl ⟨by rw [T.dir_of_mem_stickOf hmem, hdA],
          T.isLeftLeaningStack_of_sameStack hLA
            (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))⟩
  -- ### the cells of the row below the bottommost stick are anchored
  have hdown : ∀ j, j ≤ n → T.Anchored u (T.downCell u y j) := by
    intro j hj
    by_cases hjt : j ≤ n - T.idx (T.downCell u y 0)
    · have hmem := T.downCell_mem_stickOf_of_le hdC hjt
      exact Or.inl ⟨by rw [T.dir_of_mem_stickOf hmem, hdC],
        T.isLeftLeaningStack_of_sameStack hLC (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))⟩
    · push_neg at hjt
      by_cases hjw : w ≤ j
      · have hmem := T.downCell_mem_stickOf_of_ge hdw hiw hjw (by omega)
        exact Or.inl ⟨by rw [T.dir_of_mem_stickOf hmem, hdw],
          T.isLeftLeaningStack_of_sameStack hLw
            (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))⟩
      · push_neg at hjw
        have hsl : T.SlantEndBelow u (T.downCell u y j) := hrun j hjt hjw
        refine Or.inr (Or.inr ⟨walk (T.head y) u (j : ℤ),
          (T.dir_idx_rowBase hdy (by omega)).1, ?_, hsl, T.self_mem_stickOf _⟩)
        have hmemy : walk (T.head y) u (j : ℤ) ∈ T.stickOf y := by
          rw [T.mem_stickOf_iff]
          exact ⟨j, by omega, by rw [cellOfStick, hdy]⟩
        exact T.isLeftLeaningStack_of_sameStack hL
          (SameStack.trans T hy (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem hmemy).symm))
  -- ### the corner cell above the near end of the topmost stick
  have hcornermem : nbr (T.head x) (u + 4) ∈ T.stickOf (T.upCell u x s) :=
    T.backCorner_head_mem_stickOf hds his hs2
  have hcorner : T.Anchored u (nbr (T.head x) (u + 4)) :=
    Or.inl ⟨by rw [T.dir_of_mem_stickOf hcornermem, hds],
      T.isLeftLeaningStack_of_sameStack hLs
        (SameStack.symm T (T.sameStack_of_mem_stickOf hcornermem))⟩
  have hdcorner : T.dir (nbr (T.head x) (u + 4)) = u := by
    rw [T.dir_of_mem_stickOf hcornermem, hds]
  -- ### the stick flanking the far ends of the stack
  have hflankF : ∀ q ∈ T.stickOf (nbr (T.tail c) u), T.Anchored u q := by
    intro q hq
    set F := nbr (T.tail c) u with hF
    have hdF : T.dir F = u + 5 := T.dir_flank hv (by omega) hL hu
    -- the cell just below the near end of the flanking stick
    have hwalk : walk (T.head y) u (n : ℤ) = nbr (T.tail y) u := by
      rw [tail, cellOfStick, hdy, nbr_eq_walk_one, walk_walk]
      congr 1
      omega
    have hdownn : T.downCell u y n = nbr (T.head F) (u + 2) := by
      rw [downCell, hwalk, hbot]
    have hupn : nbr (T.downCell u y n) (u + 5) = T.head F := by
      rw [hdownn, nbr_nbr_cancel _ (opp_add_two u).symm]
    have hmemn := T.downCell_mem_stickOf_of_ge (j := n) hdw hiw (by omega) (by omega)
    refine Or.inr (Or.inl ⟨T.downCell u y n, by rw [T.dir_of_mem_stickOf hmemn, hdw], ?_, ?_, ?_⟩)
    · exact T.isLeftLeaningStack_of_sameStack hLw
        (SameStack.symm T (T.sameStack_of_mem_stickOf hmemn))
    · rw [hupn]
      exact Or.inr ⟨by rw [T.dir_head F, hdF], T.idx_head F⟩
    · rw [hupn, T.stickOf_eq_of_mem (T.head_mem_stickOf F)]
      exact hq
  -- ### the stick flanking the near ends of the stack
  have hflankE : ∀ q ∈ T.stickOf (nbr (T.head c) (u + 3)), T.Anchored u q := by
    intro q hq
    set q₀ := nbr (T.head x) (u + 3) with hq₀
    have hq₀mem : q₀ ∈ T.stickOf (nbr (T.head c) (u + 3)) := T.head_nbr_mem_flank hv
      (by omega) hL hu hx
    have hdq₀ : T.dir q₀ = u + 2 := by
      have h := (T.dir_beyond_ends_of_isLeftLeaningStack hv (by omega) hL hx).2
      rw [hu, opp_eq_add_three] at h
      exact h
    have hcornereq : nbr q₀ (u + 5) = nbr (T.head x) (u + 4) := by
      rw [hq₀]
      exact nbr_nbr_of_vec (T.head x) ((by decide +kernel : ∀ a : HexDir,
        (a + 3).vec + (a + 5).vec = (a + 4).vec) u)
    have hiq₀ : T.idx q₀ = 1 := by
      by_contra hcon
      have h1 : 1 < T.idx q₀ := by have := T.idx_pos q₀; omega
      have hmem := T.nbr_dir_opp_mem_stickOf q₀ h1
      rw [hdq₀, opp_add_two, hcornereq] at hmem
      have := T.dir_of_mem_stickOf hmem
      rw [hdcorner, hdq₀] at this
      exact (by decide : ∀ a : HexDir, a ≠ a + 2) u this
    have hLcorner : T.IsLeftLeaningStack (nbr (T.head x) (u + 4)) :=
      T.isLeftLeaningStack_of_sameStack hLs
        (SameStack.symm T (T.sameStack_of_mem_stickOf hcornermem))
    have hstep : nbr (nbr (T.head x) (u + 4)) (u + 2) = q₀ := by
      rw [hq₀]
      exact nbr_nbr_of_vec (T.head x) ((by decide +kernel : ∀ a : HexDir,
        (a + 4).vec + (a + 2).vec = (a + 3).vec) u)
    refine Or.inr (Or.inr ⟨nbr (T.head x) (u + 4), hdcorner, hLcorner, ?_, ?_⟩)
    · rw [hstep]
      exact Or.inl ⟨hdq₀, hiq₀⟩
    · rw [hstep, T.stickOf_eq_of_mem hq₀mem]
      exact hq
  -- ### the case analysis
  rcases T.nbr_classification hv (by omega) hL hu hx htop hy hbot hp e with
    h | h | h | ⟨j, hj, hjeq⟩ | h | ⟨j, hj, hjeq⟩
  · exact Or.inl ⟨by rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL h, hu],
      T.isLeftLeaningStack_of_sameStack hL h⟩
  · exact hflankF _ h
  · exact hflankE _ h
  · rw [hjeq]; exact hup j hj
  · rw [h]; exact hcorner
  · rw [hjeq]; exact hdown j hj

end StickTiling

end StickPolyhex
