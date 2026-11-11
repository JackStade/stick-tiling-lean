import Tiling.Proofs.Coverage

/-!
# The sticks of a vertical stack

A left-slanting stick whose lower end rests on a horizontal stick of a left-leaning stack
(`StickTiling.HoleAbove`) is one of the sticks of the vertical stack filling the space above
that stack, as described by `StickTiling.top_row_structure`.  This file shows that such a stick
really lies in a right-leaning stack, i.e. that the vertical stack contains at least two sticks,
and proves the mirror statement for `StickTiling.HoleBelow`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Positions in the row above a stack -/

/-- Two cells of the row above a stick are equal only if they are the same cell of the row. -/
lemma upCell_injective {u : HexDir} {x : Hex} {a b : ℕ} (h : T.upCell u x a = T.upCell u x b) :
    a = b := by
  have h' : walk (T.head x) u (a : ℤ) = walk (T.head x) u (b : ℤ) := by
    have := h
    simp only [upCell, nbr] at this
    exact add_right_cancel this
  have := walk_inj (T.head x) u h'
  omega

/-- Two cells of the row below a stick are equal only if they are the same cell of the row. -/
lemma downCell_injective {u : HexDir} {y : Hex} {a b : ℕ}
    (h : T.downCell u y a = T.downCell u y b) : a = b := by
  have h' : walk (T.head y) u (a : ℤ) = walk (T.head y) u (b : ℤ) := by
    have := h
    simp only [downCell, nbr] at this
    exact add_right_cancel this
  have := walk_inj (T.head y) u h'
  omega

/-- The cells of the row above the topmost stick of a stack that belong to the horizontal stick
filling the space `A` are the ones at position at least `n - i`, where `i` is the index of the
cell `A` in its stick. -/
lemma le_of_mem_stickOf_backCorner (hn : 0 < n) {u : HexDir} {x : Hex} {j : ℕ}
    (hdA : T.dir (nbr (T.tail x) (u + 5)) = u) (hdx : T.dir x = u)
    (hi : T.idx (nbr (T.tail x) (u + 5)) ≤ n)
    (hmem : T.upCell u x j ∈ T.stickOf (nbr (T.tail x) (u + 5))) :
    n - T.idx (nbr (T.tail x) (u + 5)) ≤ j := by
  set A := nbr (T.tail x) (u + 5) with hA
  set i := T.idx A with hi'
  have hAup : T.upCell u x (n - 1) = A := T.upCell_tail hdx
  have hheadA : T.head A = T.upCell u x (n - i) := by
    rw [head, hdA, ← hi', ← hAup]
    refine T.upCell_walk u x (n - 1) (-((i : ℤ) - 1)) (n - i) ?_
    have hpos : 1 ≤ i := T.idx_pos A
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : i ≤ n)]
    push_cast
    ring
  rw [T.mem_stickOf_iff] at hmem
  obtain ⟨k, hk, hkeq⟩ := hmem
  have : T.cellOfStick A k = T.upCell u x (n - i + k) := by
    rw [cellOfStick, hdA, hheadA]
    exact T.upCell_walk u x (n - i) (k : ℤ) (n - i + k) (by push_cast; ring)
  rw [this] at hkeq
  have := T.upCell_injective hkeq
  omega

/-- Conversely, the cells of the row above the topmost stick at position at least `n - i` do
belong to the horizontal stick filling the space `A`. -/
lemma upCell_mem_stickOf_backCorner (hn : 0 < n) {u : HexDir} {x : Hex} {j : ℕ}
    (hdA : T.dir (nbr (T.tail x) (u + 5)) = u) (hdx : T.dir x = u)
    (hj : n - T.idx (nbr (T.tail x) (u + 5)) ≤ j) (hjn : j < n) :
    T.upCell u x j ∈ T.stickOf (nbr (T.tail x) (u + 5)) := by
  set A := nbr (T.tail x) (u + 5) with hA
  set i := T.idx A with hi'
  have hpos : 1 ≤ i := T.idx_pos A
  have hle : i ≤ n := T.idx_le A
  have hAup : T.upCell u x (n - 1) = A := T.upCell_tail hdx
  have hheadA : T.head A = T.upCell u x (n - i) := by
    rw [head, hdA, ← hi', ← hAup]
    refine T.upCell_walk u x (n - 1) (-((i : ℤ) - 1)) (n - i) ?_
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : i ≤ n)]
    push_cast
    ring
  rw [T.mem_stickOf_iff]
  refine ⟨j - (n - i), by omega, ?_⟩
  rw [cellOfStick, hdA, hheadA]
  refine T.upCell_walk u x (n - i) ((j - (n - i) : ℕ) : ℤ) j ?_
  rw [Nat.cast_sub (by omega : n - i ≤ j)]
  ring

/-! ### The vertical stack above a left-leaning stack -/

/-- **A left-slanting stick resting on a left-leaning stack lies in a right-leaning stack.**
The vertical stack filling the space above a left-leaning stack contains at least two sticks:
in the row above the topmost stick of the stack, the ends of the left-slanting sticks form a run
of at least two cells, and two such neighbouring ends belong to sticks that are stacked. -/
theorem isRightLeaningStack_of_holeAbove (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleAbove u z) : T.IsRightLeaningStack z := by
  have h0n : 0 < n := by omega
  obtain ⟨p, hdp, hLp, hslant, hzmem⟩ := h
  -- it is enough to treat the lower end `w` of the stick
  suffices hw : T.IsRightLeaningStack (nbr p (u + 5)) by
    obtain ⟨a, b, hwa, hab⟩ := hw
    exact ⟨a, b, SameStack.trans T (T.sameStack_of_mem_stickOf hzmem) hwa, hab⟩
  set w := nbr p (u + 5) with hw
  -- the topmost stick `x` of the stack of `p`
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
  set A := nbr (T.tail x) (u + 5) with hAdef
  set i := T.idx A with hidef
  -- `w` is a cell of the row above `x`
  obtain ⟨j, hj, hjeq⟩ : ∃ j, j < n ∧ w = T.upCell u x j := by
    rcases T.up_classification hv (by omega) hLp hdp hx htop (T.sameStack_refl p) with hsame | hex
    · exfalso
      have hdw : T.dir w = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLp hsame, hdp]
      rcases hslant with ⟨hd, -⟩ | ⟨hd, -⟩
      · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdw.symm.trans hd)
      · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdw.symm.trans hd)
    · exact hex
  rw [hjeq] at hslant ⊢
  -- the structure of the row above `x`
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv (by omega) hLp hdp hx hi1 hin
  obtain ⟨hdm, him⟩ := T.top_row_base hv (by omega) hLp hdp hx hi1 hin
  set m := n - i - 1 with hmdef
  have hmn : m < n := by omega
  -- the cells of the row before `s` are horizontal, hence not slant ends
  have hnotslant : ∀ k, k ≤ s → ¬ T.SlantEndAbove u (T.upCell u x k) := by
    intro k hk hsl
    have hmem := T.upCell_mem_stickOf_of_le hds his (by omega) hk
    have hdk : T.dir (T.upCell u x k) = u := by rw [T.dir_of_mem_stickOf hmem, hds]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  -- the cells of the row beyond `m` lie on `A`, hence are not slant ends either
  have hnotslant' : ∀ k, k < n → m < k → ¬ T.SlantEndAbove u (T.upCell u x k) := by
    intro k hkn hk hsl
    have hmem : T.upCell u x k ∈ T.stickOf A :=
      T.upCell_mem_stickOf_backCorner h0n hdA hdx
        (show n - T.idx (nbr (T.tail x) (u + 5)) ≤ k by rw [← hAdef, ← hidef]; omega) hkn
    have hdk : T.dir (T.upCell u x k) = u := by rw [T.dir_of_mem_stickOf hmem, hdA]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  -- the slant ends occupy the positions `s < k ≤ m`
  have hslantrun : ∀ k, s < k → k ≤ m → T.SlantEndAbove u (T.upCell u x k) := by
    intro k hk hkm
    rcases hrow k hk (by omega) with hsl | hmem
    · exact hsl
    · have hge := T.le_of_mem_stickOf_backCorner h0n hdA hdx (T.idx_le A) hmem
      rw [← hAdef, ← hidef] at hge
      omega
  -- there are at least two slant ends
  have hsm : s + 1 < m := by
    rcases lt_or_ge (s + 1) m with h | h
    · exact h
    · exfalso
      have hs1 : s + 1 ≤ m := by
        by_contra hcon
        exact hnotslant' (s + 1) (by omega) (by omega) (Or.inr ⟨hd5, hi5⟩)
      have heq : s + 1 = m := by omega
      rw [heq] at hd5
      exact (by decide : ∀ a : HexDir, a + 5 ≠ a + 2) u (hd5.symm.trans hdm)
  -- our position is inside the run
  have hjs : s < j := by
    by_contra hcon
    exact hnotslant j (by omega) hslant
  have hjm : j ≤ m := by
    by_contra hcon
    exact hnotslant' j hj (by omega) hslant
  -- a neighbouring slant end
  rcases lt_or_ge j m with hlt | hge
  · have h1 : T.SlantEndAbove u (T.upCell u x (j + 1)) := hslantrun (j + 1) (by omega) (by omega)
    have hstep : T.upCell u x (j + 1) = nbr (T.upCell u x j) u := T.upCell_succ u x j
    rw [hstep] at h1
    exact T.isRightLeaningStack_of_slantEndAbove_nbr hslant h1
  · have hjm' : j = m := by omega
    have h0 : T.SlantEndAbove u (T.upCell u x (j - 1)) := hslantrun (j - 1) (by omega) (by omega)
    have hstep : T.upCell u x j = nbr (T.upCell u x (j - 1)) u := by
      conv_lhs => rw [show j = (j - 1) + 1 from by omega]
      exact T.upCell_succ u x (j - 1)
    have hR := T.isRightLeaningStack_of_slantEndAbove_nbr' h0 (by rw [← hstep]; exact hslant)
    rwa [← hstep] at hR

/-- Mirror image of `StickTiling.isRightLeaningStack_of_holeAbove`: a left-slanting stick
resting against a left-leaning stack from below lies in a right-leaning stack. -/
theorem isRightLeaningStack_of_holeBelow (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleBelow u z) : T.IsRightLeaningStack z := by
  have h0n : 0 < n := by omega
  obtain ⟨p, hdp, hLp, hslant, hzmem⟩ := h
  suffices hw : T.IsRightLeaningStack (nbr p (u + 2)) by
    obtain ⟨a, b, hwa, hab⟩ := hw
    exact ⟨a, b, SameStack.trans T (T.sameStack_of_mem_stickOf hzmem) hwa, hab⟩
  -- the bottommost stick `y` of the stack of `p`, and the row below it
  obtain ⟨y, hy, hne⟩ := T.exists_frontCorner_not_sameStack hv (by omega) hLp hdp
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLp hy, hdp]
  have hbot := T.tail_nbr_eq_head_flank hv (by omega) hLp hdp hy hne
  obtain ⟨hdC, hcase⟩ := T.dir_frontCorner_beyond_head hv (by omega) hLp hdp hy
  rw [← T.downCell_zero u y] at hdC hne hcase
  obtain ⟨hi1, hin⟩ : 1 < T.idx (T.downCell u y 0) ∧ T.idx (T.downCell u y 0) < n := by
    rcases hcase with ⟨-, hsame⟩ | hcase
    · exact absurd hsame hne
    · exact hcase
  obtain ⟨hdt, hit⟩ := T.downCell_tail_of_frontCorner hdC
  set t := n - T.idx (T.downCell u y 0) with htdef
  obtain ⟨w, hwt, hwn, hdw, hiw, hd2, hi2, hrun⟩ := T.bot_row_ascend hv (by omega) hdy
    (t := t) (by omega) (by omega) ⟨hdt, hit⟩
  -- our cell is a cell of the row below `y`
  obtain ⟨j, hj, hjeq⟩ : ∃ j, j < n ∧ nbr p (u + 2) = T.downCell u y j := by
    rcases T.down_classification hv (by omega) hLp hdp hy hbot (T.sameStack_refl p) with
      hsame | hex
    · exfalso
      have hdw' : T.dir (nbr p (u + 2)) = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLp hsame, hdp]
      rcases hslant with ⟨hd, -⟩ | ⟨hd, -⟩
      · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdw'.symm.trans hd)
      · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdw'.symm.trans hd)
    · exact hex
  rw [hjeq] at hslant ⊢
  -- the cells of the row before `t` belong to the horizontal stick beyond the near end
  have hnotslant : ∀ k, k ≤ t → ¬ T.SlantEndBelow u (T.downCell u y k) := by
    intro k hk hsl
    have hmem := T.downCell_mem_stickOf_of_le hdC (by omega)
    have hdk : T.dir (T.downCell u y k) = u := by rw [T.dir_of_mem_stickOf hmem, hdC]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  -- the cells of the row from `w` on belong to the second horizontal stick below
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
  -- the first left-slanting stick of the row carries its arrow the other way round
  have hfirst : T.dir (T.downCell u y (t + 1)) = u + 5 := by
    have hpred : nbr (walk (T.head y) u ((t + 1 : ℕ) : ℤ)) (u + 3) = walk (T.head y) u (t : ℤ) := by
      rw [walk_nat_succ]
      exact nbr_nbr_cancel _ (opp_eq_add_three u).symm
    obtain ⟨hdb, hib⟩ := T.dir_idx_rowBase hdy (j := t + 1) (by omega)
    have hstep := T.bot_step_tail hv (by omega) hdb (by omega)
      (by rw [hpred]; exact hdt) (by rw [hpred]; exact hit)
    exact hstep.2.1
  have hrun2 : t + 1 < w - 1 := by
    rcases Nat.lt_or_ge (t + 1) (w - 1) with h | h
    · exact h
    · exfalso
      have heq : t + 1 = w - 1 := by omega
      rw [heq] at hfirst
      exact (by decide : ∀ a : HexDir, a + 5 ≠ a + 2) u (hfirst.symm.trans hd2)
  -- a neighbouring left-slanting stick of the same vertical stack
  rcases Nat.lt_or_ge (j + 1) w with hlt | hge
  · have h1 : T.SlantEndBelow u (T.downCell u y (j + 1)) := hrun (j + 1) (by omega) hlt
    have hstep : T.downCell u y (j + 1) = nbr (T.downCell u y j) u := T.downCell_succ u y j
    rw [hstep] at h1
    exact T.isRightLeaningStack_of_slantEndBelow_nbr hslant h1
  · have hjw' : j = w - 1 := by omega
    have h0 : T.SlantEndBelow u (T.downCell u y (j - 1)) := hrun (j - 1) (by omega) (by omega)
    have hstep : T.downCell u y j = nbr (T.downCell u y (j - 1)) u := by
      conv_lhs => rw [show j = (j - 1) + 1 from by omega]
      exact T.downCell_succ u y (j - 1)
    have hR := T.isRightLeaningStack_of_slantEndBelow_nbr' h0 (by rw [← hstep]; exact hslant)
    rwa [← hstep] at hR

/-- An anchored cell is a weave cell. -/
theorem weaveCell_of_anchored (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.Anchored u z) : T.WeaveCell u z := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨T.slantsLeft_of_holeAbove h, T.isRightLeaningStack_of_holeAbove hv hn h⟩
  · exact Or.inr ⟨T.slantsLeft_of_holeBelow h, T.isRightLeaningStack_of_holeBelow hv hn h⟩

end StickTiling

end StickPolyhex
