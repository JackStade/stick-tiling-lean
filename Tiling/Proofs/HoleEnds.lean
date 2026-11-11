import Tiling.Proofs.HoleStacks

/-!
# The two ends of a stick of a vertical stack

A left-slanting stick resting on a left-leaning stack from above (`StickTiling.HoleAbove`) also
rests against a left-leaning stack from below (`StickTiling.HoleBelow`), and conversely: the
cells just beyond the two ends of a stick of a vertical stack are covered by horizontal sticks
of direction `u` lying in left-leaning stacks.

For the upper end this is the last step of the induction of Figure 18 of the paper.  The
argument walks along the row of cells just above the upper ends of the sticks of the vertical
stack.  Its right-hand end is pinned down by the stack filling the space `A`: the rightmost
stick of the vertical stack is the stick flanking the near ends of the sticks of that stack, so
the cell above its upper end is the corner cell beyond the near end of the topmost stick of that
stack, which belongs to a further left-leaning stack.  From there one walks leftwards: the cell
above the upper end of a stick of a vertical stack is always horizontal, because the cells
beyond the ends of a stacked stick are parallel to the stacking direction, and a horizontal cell
just beyond the near end of a left-leaning stack is impossible.

The lower ends are treated by the mirror-image argument, starting from the stick flanking the
far ends of the sticks of the stack below.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### The ends of a left-slanting stick -/

/-- The near end of a left-slanting stick of direction `u + 2` whose last cell is given. -/
lemma head_eq_walk_of_dir_add_two {u : HexDir} {z : Hex} (hd : T.dir z = u + 2)
    (hi : T.idx z = n) : T.head z = walk z (u + 5) ((n : ℤ) - 1) := by
  have h5 : u + 5 = (u + 2).opp := by
    rw [opp_eq_add_three]
    exact ((by decide : ∀ a : HexDir, a + 5 = a + 2 + 3) u)
  rw [head, hd, hi, h5, walk_opp]

/-- The far end of a left-slanting stick of direction `u + 5` whose first cell is given. -/
lemma tail_eq_walk_of_dir_add_five (hn : 0 < n) {u : HexDir} {z : Hex} (hd : T.dir z = u + 5)
    (hi : T.idx z = 1) : T.tail z = walk z (u + 5) ((n : ℤ) - 1) := by
  have hhead : T.head z = z := by rw [head, hi]; simp [walk]
  rw [tail, cellOfStick, hhead, hd, show (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 from by omega]

/-- The near end of a left-slanting stick of direction `u + 5` whose last cell is given. -/
lemma head_eq_walk_of_dir_add_five {u : HexDir} {z : Hex} (hd : T.dir z = u + 5)
    (hi : T.idx z = n) : T.head z = walk z (u + 2) ((n : ℤ) - 1) := by
  have h2 : u + 2 = (u + 5).opp := by
    rw [opp_eq_add_three]
    exact ((by decide : ∀ a : HexDir, a + 2 = a + 5 + 3) u)
  rw [head, hd, hi, h2, walk_opp]

/-- The far end of a left-slanting stick of direction `u + 2` whose first cell is given. -/
lemma tail_eq_walk_of_dir_add_two (hn : 0 < n) {u : HexDir} {z : Hex} (hd : T.dir z = u + 2)
    (hi : T.idx z = 1) : T.tail z = walk z (u + 2) ((n : ℤ) - 1) := by
  have hhead : T.head z = z := by rw [head, hi]; simp [walk]
  rw [tail, cellOfStick, hhead, hd, show (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 from by omega]

/-- The cell `n - 1` steps up from the lower end of a left-slanting stick is its upper end. -/
lemma slantEndBelow_topCell (hn : 0 < n) {u : HexDir} {z : Hex} (h : T.SlantEndAbove u z) :
    T.SlantEndBelow u (walk z (u + 5) ((n : ℤ) - 1)) ∧
      walk z (u + 5) ((n : ℤ) - 1) ∈ T.stickOf z := by
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · rw [← T.head_eq_walk_of_dir_add_two hd hi]
    exact ⟨Or.inl ⟨by rw [T.dir_head, hd], T.idx_head z⟩, T.head_mem_stickOf z⟩
  · rw [← T.tail_eq_walk_of_dir_add_five hn hd hi]
    exact ⟨Or.inr ⟨by rw [T.dir_tail hn, hd], T.idx_tail hn z⟩, T.tail_mem_stickOf hn z⟩

/-- The cell `n - 1` steps down from the upper end of a left-slanting stick is its lower end. -/
lemma slantEndAbove_botCell (hn : 0 < n) {u : HexDir} {z : Hex} (h : T.SlantEndBelow u z) :
    T.SlantEndAbove u (walk z (u + 2) ((n : ℤ) - 1)) ∧
      walk z (u + 2) ((n : ℤ) - 1) ∈ T.stickOf z := by
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · rw [← T.tail_eq_walk_of_dir_add_two hn hd hi]
    exact ⟨Or.inl ⟨by rw [T.dir_tail hn, hd], T.idx_tail hn z⟩, T.tail_mem_stickOf hn z⟩
  · rw [← T.head_eq_walk_of_dir_add_five hd hi]
    exact ⟨Or.inr ⟨by rw [T.dir_head, hd], T.idx_head z⟩, T.head_mem_stickOf z⟩

/-- Two directions on the axis of `u` are horizontal. -/
lemma horizontal_of_sameAxis {u e d : HexDir} (hax : SameAxis u e) (h : SameAxis e d) :
    d = u ∨ d = u + 3 := by
  revert hax h; revert u e d; decide

/-- **The cell above the upper end of a stick of a vertical stack is horizontal.**  It lies
just beyond an end of a stick that is stacked in a direction parallel to `u`, hence its
direction is parallel to `u`. -/
lemma dir_above_topCell (hv : T.SatisfiesWeaveRules) (hn : 0 < n) {u e : HexDir} {z z' : Hex}
    (h : T.SlantEndAbove u z) (hax : SameAxis u e) (hst : T.StackedBy z z' e) :
    T.dir (walk z (u + 5) (n : ℤ)) = u ∨ T.dir (walk z (u + 5) (n : ℤ)) = u + 3 := by
  obtain ⟨h1, h2⟩ := T.sameAxis_dir_nbr_ends_of_stackedBy hv hn hst
  have hstep : walk z (u + 5) (n : ℤ) = nbr (walk z (u + 5) ((n : ℤ) - 1)) (u + 5) := by
    rw [← walk_succ]
    congr 1
    ring
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · rw [hd, opp_add_two] at h2
    rw [hstep, ← T.head_eq_walk_of_dir_add_two hd hi]
    exact horizontal_of_sameAxis hax h2
  · rw [hd] at h1
    rw [hstep, ← T.tail_eq_walk_of_dir_add_five hn hd hi]
    exact horizontal_of_sameAxis hax h1

/-- **The cell below the lower end of a stick of a vertical stack is horizontal.** -/
lemma dir_below_botCell (hv : T.SatisfiesWeaveRules) (hn : 0 < n) {u e : HexDir} {z z' : Hex}
    (h : T.SlantEndBelow u z) (hax : SameAxis u e) (hst : T.StackedBy z z' e) :
    T.dir (walk z (u + 2) (n : ℤ)) = u ∨ T.dir (walk z (u + 2) (n : ℤ)) = u + 3 := by
  obtain ⟨h1, h2⟩ := T.sameAxis_dir_nbr_ends_of_stackedBy hv hn hst
  have hstep : walk z (u + 2) (n : ℤ) = nbr (walk z (u + 2) ((n : ℤ) - 1)) (u + 2) := by
    rw [← walk_succ]
    congr 1
    ring
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · rw [hd] at h1
    rw [hstep, ← T.tail_eq_walk_of_dir_add_two hn hd hi]
    exact horizontal_of_sameAxis hax h1
  · rw [hd, opp_add_five] at h2
    rw [hstep, ← T.head_eq_walk_of_dir_add_five hd hi]
    exact horizontal_of_sameAxis hax h2

/-! ### The two ends of the sticks flanking a left-leaning stack -/

/-- **The cell above the upper end of the stick flanking the near ends of a left-leaning
stack.**  It is the corner cell beyond the near end of the topmost stick of the stack, which
belongs to the second left-leaning stack above. -/
lemma above_head_flank (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {c : Hex} (hu : T.dir c = u)
    (hL : T.IsLeftLeaningStack c) :
    T.dir (nbr (T.head (nbr (T.head c) (u + 3))) (u + 5)) = u ∧
      T.IsLeftLeaningStack (nbr (T.head (nbr (T.head c) (u + 3))) (u + 5)) ∧
      T.StackAbove u c (nbr (T.head (nbr (T.head c) (u + 3))) (u + 5)) := by
  obtain ⟨x, hx, hnex⟩ := T.exists_backCorner_not_sameStack hv (by omega) hL hu
  obtain ⟨hdA, hcaseA⟩ := T.dir_backCorner_beyond_tail hv (by omega) hL hu hx
  obtain ⟨hi1, hin⟩ :
      1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n := by
    rcases hcaseA with ⟨-, hsame⟩ | hcaseA
    · exact absurd hsame hnex
    · exact hcaseA
  obtain ⟨s, hs2, hds, his, hd5, hi5, -⟩ :=
    T.top_row_structure hv (by omega) hL hu hx hi1 hin
  have hLs : T.IsLeftLeaningStack (T.upCell u x s) :=
    T.isLeftLeaningStack_upCell hv (by omega) hds his hd5 hi5
  have hcornermem : nbr (T.head x) (u + 4) ∈ T.stickOf (T.upCell u x s) :=
    T.backCorner_head_mem_stickOf hds his hs2
  have hdcorner : T.dir (nbr (T.head x) (u + 4)) = u := by
    rw [T.dir_of_mem_stickOf hcornermem, hds]
  have hLcorner : T.IsLeftLeaningStack (nbr (T.head x) (u + 4)) :=
    T.isLeftLeaningStack_of_sameStack hLs
      (SameStack.symm T (T.sameStack_of_mem_stickOf hcornermem))
  have hq₀mem : nbr (T.head x) (u + 3) ∈ T.stickOf (nbr (T.head c) (u + 3)) :=
    T.head_nbr_mem_flank hv (by omega) hL hu hx
  have hdF : T.dir (nbr (T.head c) (u + 3)) = u + 2 := by
    have h := (T.dir_beyond_ends_of_isLeftLeaningStack hv (by omega) hL (T.sameStack_refl c)).2
    rw [hu, opp_eq_add_three] at h
    exact h
  have hdq₀ : T.dir (nbr (T.head x) (u + 3)) = u + 2 := by
    rw [T.dir_of_mem_stickOf hq₀mem, hdF]
  have hcornereq : nbr (nbr (T.head x) (u + 3)) (u + 5) = nbr (T.head x) (u + 4) :=
    nbr_nbr_of_vec (T.head x) ((by decide +kernel : ∀ a : HexDir,
      (a + 3).vec + (a + 5).vec = (a + 4).vec) u)
  have hiq₀ : T.idx (nbr (T.head x) (u + 3)) = 1 := by
    by_contra hcon
    have h1 : 1 < T.idx (nbr (T.head x) (u + 3)) := by
      have := T.idx_pos (nbr (T.head x) (u + 3)); omega
    have hmem := T.nbr_dir_opp_mem_stickOf (nbr (T.head x) (u + 3)) h1
    rw [hdq₀, opp_add_two, hcornereq] at hmem
    have hd := T.dir_of_mem_stickOf hmem
    rw [hdcorner, hdq₀] at hd
    exact (by decide : ∀ a : HexDir, a ≠ a + 2) u hd
  have hhead : T.head (nbr (T.head c) (u + 3)) = nbr (T.head x) (u + 3) :=
    (T.eq_head_of_mem_of_idx_eq hq₀mem hiq₀).symm
  have hAbove : T.StackAbove u c (nbr (T.head x) (u + 4)) := by
    refine ⟨?_, T.head x, SameStack.trans T hx (T.sameStack_of_stickOf_eq
      (T.stickOf_eq_of_mem (T.head_mem_stickOf x)).symm), Or.inl (T.sameStack_refl _)⟩
    intro hsame
    exact T.not_sameStack_upCell hv (by omega) hL hu hx hds his hs2
      (SameStack.trans T hsame (T.sameStack_of_mem_stickOf hcornermem))
  rw [hhead, hcornereq]
  exact ⟨hdcorner, hLcorner, hAbove⟩

/-- **The cell below the lower end of the stick flanking the far ends of a left-leaning
stack.**  It is the cell of the second left-leaning stack below whose near end lies beyond the
far end of the bottommost stick of the stack. -/
lemma below_tail_flank (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {c : Hex} (hu : T.dir c = u)
    (hL : T.IsLeftLeaningStack c) :
    T.dir (nbr (T.head (nbr (T.tail c) u)) (u + 2)) = u ∧
      T.IsLeftLeaningStack (nbr (T.head (nbr (T.tail c) u)) (u + 2)) := by
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
  obtain ⟨hdt, hit⟩ := T.downCell_tail_of_frontCorner hdC
  obtain ⟨w, hwt, hwn, hdw, hiw, hd2, hi2, -⟩ := T.bot_row_ascend hv (by omega) hdy
    (t := n - T.idx (T.downCell u y 0)) (by omega) (by omega) ⟨hdt, hit⟩
  have hLw : T.IsLeftLeaningStack (T.downCell u y w) :=
    T.isLeftLeaningStack_downCell hv (by omega) (by omega) hdw hiw hd2 hi2
  have hwalk : walk (T.head y) u (n : ℤ) = nbr (T.tail y) u := by
    rw [tail, cellOfStick, hdy, nbr_eq_walk_one, walk_walk]
    congr 1
    omega
  have hdownn : T.downCell u y n = nbr (T.head (nbr (T.tail c) u)) (u + 2) := by
    rw [downCell, hwalk, hbot]
  have hmemn := T.downCell_mem_stickOf_of_ge (j := n) hdw hiw (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [← hdownn, T.dir_of_mem_stickOf hmemn, hdw]
  · rw [← hdownn]
    exact T.isLeftLeaningStack_of_sameStack hLw
      (SameStack.symm T (T.sameStack_of_mem_stickOf hmemn))

/-! ### The ends of a stick of a vertical stack -/

/-- **The cell above the upper end of a stick of a vertical stack.**  It is a horizontal cell of
direction `u` lying in a left-leaning stack.  The proof walks leftwards along the row of cells
above the upper ends of the sticks of the vertical stack, starting from its rightmost stick,
which flanks the near ends of the sticks of the stack filling the space `A`. -/
theorem dir_isLeftLeaning_above_topCell (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hLp : T.IsLeftLeaningStack p)
    (hslant : T.SlantEndAbove u (nbr p (u + 5))) :
    T.dir (walk (nbr p (u + 5)) (u + 5) (n : ℤ)) = u ∧
      T.IsLeftLeaningStack (walk (nbr p (u + 5)) (u + 5) (n : ℤ)) := by
  have h0n : 0 < n := by omega
  set v := nbr p (u + 5) with hvdef
  -- the topmost stick of the stack of `p` and the row above it
  obtain ⟨x, hx, hne⟩ := T.exists_backCorner_not_sameStack hv (by omega) hLp hdp
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLp hx, hdp]
  have htop := T.tail_nbr_eq_tail_flank hv (by omega) hLp hdp hx hne
  obtain ⟨hdA, hcase⟩ := T.dir_backCorner_beyond_tail hv (by omega) hLp hdp hx
  obtain ⟨hi1, hin⟩ :
      1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n := by
    rcases hcase with ⟨-, hsame⟩ | hcase
    · exact absurd hsame hne
    · exact hcase
  have hLA : T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)) := by
    rcases T.isLeftLeaningStack_backCorner hv (by omega) hLp hdp hx with h | h
    · exact absurd h hne
    · exact h
  set A := nbr (T.tail x) (u + 5) with hAdef
  set i := T.idx A with hidef
  have hle : i ≤ n := T.idx_le A
  -- our stick is one of the cells of the row above the topmost stick
  obtain ⟨j, hj, hjeq⟩ : ∃ j, j < n ∧ v = T.upCell u x j := by
    rcases T.up_classification hv (by omega) hLp hdp hx htop (T.sameStack_refl p) with hsame | hex
    · exfalso
      have hdv : T.dir v = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLp hsame, hdp]
      rcases hslant with ⟨hd, -⟩ | ⟨hd, -⟩
      · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdv.symm.trans hd)
      · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdv.symm.trans hd)
    · exact hex
  rw [hjeq] at hslant ⊢
  -- the structure of the row above the topmost stick
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv (by omega) hLp hdp hx hi1 hin
  obtain ⟨hdm, him⟩ := T.top_row_base hv (by omega) hLp hdp hx hi1 hin
  set m := n - i - 1 with hmdef
  have hmn : m < n := by omega
  have hnotslant : ∀ k, k ≤ s → ¬ T.SlantEndAbove u (T.upCell u x k) := by
    intro k hk hsl
    have hmem := T.upCell_mem_stickOf_of_le hds his (by omega) hk
    have hdk : T.dir (T.upCell u x k) = u := by rw [T.dir_of_mem_stickOf hmem, hds]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  have hnotslant' : ∀ k, k < n → m < k → ¬ T.SlantEndAbove u (T.upCell u x k) := by
    intro k hkn hk hsl
    have hmem : T.upCell u x k ∈ T.stickOf A :=
      T.upCell_mem_stickOf_backCorner h0n hdA hdx
        (show n - T.idx (nbr (T.tail x) (u + 5)) ≤ k by rw [← hAdef, ← hidef]; omega) hkn
    have hdk : T.dir (T.upCell u x k) = u := by rw [T.dir_of_mem_stickOf hmem, hdA]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  have hslantrun : ∀ k, s < k → k ≤ m → T.SlantEndAbove u (T.upCell u x k) := by
    intro k hk hkm
    rcases hrow k hk (by omega) with hsl | hmem
    · exact hsl
    · have hge := T.le_of_mem_stickOf_backCorner h0n hdA hdx (T.idx_le A) hmem
      rw [← hAdef, ← hidef] at hge
      omega
  have hjs : s < j := by
    by_contra hcon
    exact hnotslant j (by omega) hslant
  have hjm : j ≤ m := by
    by_contra hcon
    exact hnotslant' j hj (by omega) hslant
  -- the base of the induction: the rightmost stick of the vertical stack
  have hbase : T.dir (walk (T.upCell u x m) (u + 5) (n : ℤ)) = u ∧
      T.IsLeftLeaningStack (walk (T.upCell u x m) (u + 5) (n : ℤ)) := by
    have hAup : T.upCell u x (n - 1) = A := T.upCell_tail hdx
    have hheadA : T.head A = T.upCell u x (n - i) := by
      rw [head, hdA, ← hidef, ← hAup]
      refine T.upCell_walk u x (n - 1) (-((i : ℤ) - 1)) (n - i) ?_
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : i ≤ n)]
      push_cast
      ring
    have hmA : T.upCell u x m = nbr (T.head A) (u + 3) := by
      rw [hheadA, show n - i = m + 1 from by omega]
      exact (T.upCell_pred u x m).symm
    have hkey := T.above_head_flank hv hn hdA hLA
    rw [← hmA] at hkey
    have hcell : nbr (walk (T.upCell u x m) (u + 5) ((n : ℤ) - 1)) (u + 5)
        = walk (T.upCell u x m) (u + 5) (n : ℤ) := by
      rw [← walk_succ]
      congr 1
      ring
    rw [T.head_eq_walk_of_dir_add_two hdm him, hcell] at hkey
    exact ⟨hkey.1, hkey.2.1⟩
  -- walking leftwards along the row above the upper ends
  have key : ∀ d k, k + d = m → s < k →
      T.dir (walk (T.upCell u x k) (u + 5) (n : ℤ)) = u ∧
        T.IsLeftLeaningStack (walk (T.upCell u x k) (u + 5) (n : ℤ)) := by
    intro d
    induction d with
    | zero =>
      intro k hk _
      rw [show k = m from by omega]
      exact hbase
    | succ d ih =>
      intro k hk hsk
      obtain ⟨hd', hL'⟩ := ih (k + 1) (by omega) (by omega)
      have hsl1 : T.SlantEndAbove u (T.upCell u x k) := hslantrun k hsk (by omega)
      have hsl2 : T.SlantEndAbove u (nbr (T.upCell u x k) u) := by
        rw [← T.upCell_succ]
        exact hslantrun (k + 1) (by omega) (by omega)
      have hst := T.stackedBy_of_slantEndAbove_nbr hsl1 hsl2
      have hdir := T.dir_above_topCell hv h0n hsl1 (Or.inl rfl) hst
      have hgstep : walk (T.upCell u x (k + 1)) (u + 5) (n : ℤ)
          = nbr (walk (T.upCell u x k) (u + 5) (n : ℤ)) u := by
        rw [T.upCell_succ, walk_nbr_comm]
      rw [hgstep] at hd' hL'
      set g := walk (T.upCell u x k) (u + 5) (n : ℤ) with hgdef
      have hback : nbr (nbr g u) (u + 3) = g := nbr_nbr_cancel g (opp_eq_add_three u).symm
      have hidxne : T.idx (nbr g u) ≠ 1 := by
        intro hone
        have hhead : T.head (nbr g u) = nbr g u := by rw [head, hone]; simp [walk]
        have hb :=
          (T.dir_beyond_ends_of_isLeftLeaningStack hv (by omega) hL' (T.sameStack_refl _)).2
        rw [hd', opp_eq_add_three, hhead, hback] at hb
        rcases hdir with h | h
        · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (h.symm.trans hb)
        · exact (by decide : ∀ a : HexDir, a + 3 ≠ a + 2) u (h.symm.trans hb)
      have h1lt : 1 < T.idx (nbr g u) := by
        have := T.idx_pos (nbr g u); omega
      have hmem := T.nbr_dir_opp_mem_stickOf (nbr g u) h1lt
      rw [hd', opp_eq_add_three, hback] at hmem
      exact ⟨by rw [T.dir_of_mem_stickOf hmem, hd'],
        T.isLeftLeaningStack_of_sameStack hL'
          (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))⟩
  exact key (m - j) j (by omega) hjs

/-- **The cell below the lower end of a stick of a vertical stack.**  Mirror image of
`StickTiling.dir_isLeftLeaning_above_topCell`: the walk starts from the leftmost stick of the
vertical stack, which flanks the far ends of the sticks of the stack below, and proceeds
rightwards. -/
theorem dir_isLeftLeaning_below_botCell (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {q : Hex}
    (hdq : T.dir q = u) (hLq : T.IsLeftLeaningStack q)
    (hslant : T.SlantEndBelow u (nbr q (u + 2))) :
    T.dir (walk (nbr q (u + 2)) (u + 2) (n : ℤ)) = u ∧
      T.IsLeftLeaningStack (walk (nbr q (u + 2)) (u + 2) (n : ℤ)) := by
  have h0n : 0 < n := by omega
  set v := nbr q (u + 2) with hvdef
  -- the bottommost stick of the stack of `q` and the row below it
  obtain ⟨y, hy, hne⟩ := T.exists_frontCorner_not_sameStack hv (by omega) hLq hdq
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLq hy, hdq]
  have hbot := T.tail_nbr_eq_head_flank hv (by omega) hLq hdq hy hne
  obtain ⟨hdC, hcase⟩ := T.dir_frontCorner_beyond_head hv (by omega) hLq hdq hy
  rw [← T.downCell_zero u y] at hdC hne hcase
  obtain ⟨hi1, hin⟩ : 1 < T.idx (T.downCell u y 0) ∧ T.idx (T.downCell u y 0) < n := by
    rcases hcase with ⟨-, hsame⟩ | hcase
    · exact absurd hsame hne
    · exact hcase
  have hLC : T.IsLeftLeaningStack (T.downCell u y 0) := by
    rcases T.isLeftLeaningStack_frontCorner hv (by omega) hLq hdq hy with h | h
    · rw [← T.downCell_zero u y] at h
      exact absurd h hne
    · rw [← T.downCell_zero u y] at h
      exact h
  obtain ⟨hdt, hit⟩ := T.downCell_tail_of_frontCorner hdC
  set t := n - T.idx (T.downCell u y 0) with htdef
  obtain ⟨w, hwt, hwn, hdw, hiw, hd2, hi2, hrun⟩ := T.bot_row_ascend hv (by omega) hdy
    (t := t) (by omega) (by omega) ⟨hdt, hit⟩
  -- our stick is one of the cells of the row below the bottommost stick
  obtain ⟨j, hj, hjeq⟩ : ∃ j, j < n ∧ v = T.downCell u y j := by
    rcases T.down_classification hv (by omega) hLq hdq hy hbot (T.sameStack_refl q) with
      hsame | hex
    · exfalso
      have hdv : T.dir v = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLq hsame, hdq]
      rcases hslant with ⟨hd, -⟩ | ⟨hd, -⟩
      · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdv.symm.trans hd)
      · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdv.symm.trans hd)
    · exact hex
  rw [hjeq] at hslant ⊢
  have hnotslant : ∀ k, k ≤ t → ¬ T.SlantEndBelow u (T.downCell u y k) := by
    intro k hk hsl
    have hmem := T.downCell_mem_stickOf_of_le hdC (by omega)
    have hdk : T.dir (T.downCell u y k) = u := by rw [T.dir_of_mem_stickOf hmem, hdC]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  have hnotslant' : ∀ k, k < n → w ≤ k → ¬ T.SlantEndBelow u (T.downCell u y k) := by
    intro k hkn hk hsl
    have hmem := T.downCell_mem_stickOf_of_ge hdw hiw hk (by omega)
    have hdk : T.dir (T.downCell u y k) = u := by rw [T.dir_of_mem_stickOf hmem, hdw]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  have hjt : t < j := by
    by_contra hcon
    exact hnotslant j (by omega) hslant
  have hjw : j < w := by
    by_contra hcon
    exact hnotslant' j hj (by omega) hslant
  -- the base of the induction: the leftmost stick of the vertical stack
  have hbase : T.dir (walk (T.downCell u y (t + 1)) (u + 2) (n : ℤ)) = u ∧
      T.IsLeftLeaningStack (walk (T.downCell u y (t + 1)) (u + 2) (n : ℤ)) := by
    have hmemt := T.downCell_mem_stickOf_of_le hdC (le_refl t)
    have htailC : T.downCell u y t = T.tail (T.downCell u y 0) :=
      T.eq_tail_of_mem_of_idx_eq h0n hmemt hit
    have hstep : T.downCell u y (t + 1) = nbr (T.tail (T.downCell u y 0)) u := by
      rw [← htailC]
      exact T.downCell_succ u y t
    have hd5 : T.dir (T.downCell u y (t + 1)) = u + 5 := by
      rw [hstep]
      exact T.dir_flank hv (by omega) hLC hdC
    have hitop : T.idx (T.downCell u y (t + 1)) = n := by
      rcases hrun (t + 1) (by omega) (by omega) with ⟨hd, -⟩ | ⟨-, hi⟩
      · exact absurd (hd5.symm.trans hd) ((by decide : ∀ a : HexDir, a + 5 ≠ a + 2) u)
      · exact hi
    have hkey := T.below_tail_flank hv hn hdC hLC
    rw [← hstep] at hkey
    have hcell : nbr (walk (T.downCell u y (t + 1)) (u + 2) ((n : ℤ) - 1)) (u + 2)
        = walk (T.downCell u y (t + 1)) (u + 2) (n : ℤ) := by
      rw [← walk_succ]
      congr 1
      ring
    rw [T.head_eq_walk_of_dir_add_five hd5 hitop, hcell] at hkey
    exact hkey
  -- walking rightwards along the row below the lower ends
  have key : ∀ d k, k = t + 1 + d → k < w →
      T.dir (walk (T.downCell u y k) (u + 2) (n : ℤ)) = u ∧
        T.IsLeftLeaningStack (walk (T.downCell u y k) (u + 2) (n : ℤ)) := by
    intro d
    induction d with
    | zero =>
      intro k hk _
      rw [show k = t + 1 from by omega]
      exact hbase
    | succ d ih =>
      intro k hk hkw
      obtain ⟨hd', hL'⟩ := ih (k - 1) (by omega) (by omega)
      have hsl0 : T.SlantEndBelow u (T.downCell u y (k - 1)) := hrun (k - 1) (by omega) (by omega)
      have hsl1 : T.SlantEndBelow u (nbr (T.downCell u y (k - 1)) u) := by
        rw [← T.downCell_succ, show k - 1 + 1 = k from by omega]
        exact hrun k (by omega) hkw
      have hst := T.stackedBy_of_slantEndBelow_nbr hsl0 hsl1
      have hkstep : T.downCell u y k = nbr (T.downCell u y (k - 1)) u := by
        rw [← T.downCell_succ, show k - 1 + 1 = k from by omega]
      have hdir : T.dir (walk (T.downCell u y k) (u + 2) (n : ℤ)) = u ∨
          T.dir (walk (T.downCell u y k) (u + 2) (n : ℤ)) = u + 3 := by
        rw [hkstep]
        exact T.dir_below_botCell hv h0n (by rw [← hkstep]; exact hrun k (by omega) hkw)
          (Or.inr rfl) (StackedBy.symm T hst)
      have hgstep : walk (T.downCell u y k) (u + 2) (n : ℤ)
          = nbr (walk (T.downCell u y (k - 1)) (u + 2) (n : ℤ)) u := by
        rw [hkstep, walk_nbr_comm]
      set g := walk (T.downCell u y (k - 1)) (u + 2) (n : ℤ) with hgdef
      rw [hgstep] at hdir ⊢
      have hidxne : T.idx g ≠ n := by
        intro hfull
        have htail : T.tail g = g :=
          (T.eq_tail_of_mem_of_idx_eq h0n (T.self_mem_stickOf g) hfull).symm
        have hb := T.dir_flank hv (by omega) hL' hd'
        rw [htail] at hb
        rcases hdir with h | h
        · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (h.symm.trans hb)
        · exact (by decide : ∀ a : HexDir, a + 3 ≠ a + 5) u (h.symm.trans hb)
      have hlt : T.idx g < n := by
        have := T.idx_le g; omega
      have hmem := T.nbr_dir_mem_stickOf g hlt
      rw [hd'] at hmem
      exact ⟨by rw [T.dir_of_mem_stickOf hmem, hd'],
        T.isLeftLeaningStack_of_sameStack hL'
          (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))⟩
  exact key (j - t - 1) j (by omega) hjw

/-! ### The two ends of a stick of a vertical stack -/

/-- **A stick of a vertical stack is also covered at its upper end.**  A left-slanting stick
resting on a left-leaning stack from above rests against a left-leaning stack from below. -/
theorem holeBelow_of_holeAbove (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleAbove u z) : T.HoleBelow u z := by
  obtain ⟨p, hdp, hLp, hslant, hzmem⟩ := h
  obtain ⟨hdg, hLg⟩ := T.dir_isLeftLeaning_above_topCell hv hn hdp hLp hslant
  obtain ⟨hsb, hmem⟩ := T.slantEndBelow_topCell (by omega) hslant
  have hback : nbr (walk (nbr p (u + 5)) (u + 5) (n : ℤ)) (u + 2)
      = walk (nbr p (u + 5)) (u + 5) ((n : ℤ) - 1) := by
    rw [show walk (nbr p (u + 5)) (u + 5) (n : ℤ)
        = nbr (walk (nbr p (u + 5)) (u + 5) ((n : ℤ) - 1)) (u + 5) from by
      rw [← walk_succ]; congr 1; ring]
    exact nbr_nbr_cancel _ (opp_add_five u).symm
  refine ⟨walk (nbr p (u + 5)) (u + 5) (n : ℤ), hdg, hLg, ?_, ?_⟩
  · rw [hback]
    exact hsb
  · rw [hback, T.stickOf_eq_of_mem hmem]
    exact hzmem

/-- **A stick of a vertical stack is also covered at its lower end.**  Mirror image of
`StickTiling.holeBelow_of_holeAbove`. -/
theorem holeAbove_of_holeBelow (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleBelow u z) : T.HoleAbove u z := by
  obtain ⟨q, hdq, hLq, hslant, hzmem⟩ := h
  obtain ⟨hdg, hLg⟩ := T.dir_isLeftLeaning_below_botCell hv hn hdq hLq hslant
  obtain ⟨hsa, hmem⟩ := T.slantEndAbove_botCell (by omega) hslant
  have hback : nbr (walk (nbr q (u + 2)) (u + 2) (n : ℤ)) (u + 5)
      = walk (nbr q (u + 2)) (u + 2) ((n : ℤ) - 1) := by
    rw [show walk (nbr q (u + 2)) (u + 2) (n : ℤ)
        = nbr (walk (nbr q (u + 2)) (u + 2) ((n : ℤ) - 1)) (u + 2) from by
      rw [← walk_succ]; congr 1; ring]
    exact nbr_nbr_cancel _ (opp_add_two u).symm
  refine ⟨walk (nbr q (u + 2)) (u + 2) (n : ℤ), hdg, hLg, ?_, ?_⟩
  · rw [hback]
    exact hsa
  · rw [hback, T.stickOf_eq_of_mem hmem]
    exact hzmem

end StickTiling

end StickPolyhex
