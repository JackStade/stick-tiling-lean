import Tiling.Proofs.StackTop
import Tiling.Proofs.WeaveDown

/-!
# The structure of the row below a left-leaning stack

Mirror image of `Tiling/Proofs/StackTop.lean`.  Using the local steps of
`Tiling/Proofs/BottomRow.lean` we determine the whole row of cells lying on the front side of
the bottom stick of a left-leaning stack: reading it from the near end towards the far end one
meets first the horizontal stick filling the space beyond the near end, then the ends of the
left-slanting sticks of a vertical stack, and finally a second horizontal stick.  Consequently
every left-leaning stack has two left-leaning stacks below it.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### The cells of the row below a stick -/

/-- The `j`-th cell of the row lying on the front side of the stick through `y` (for a stick of
direction `u`): the cell just below the `j`-th cell of that stick. -/
def downCell (u : HexDir) (y : Hex) (j : ℕ) : Hex := nbr (walk (T.head y) u j) (u + 2)

/-- A cell of the row below a stack which is the end of a left-slanting stick: either the first
cell of a stick of direction `u + 2` or the last cell of a stick of direction `u + 5`. -/
def SlantEndBelow (u : HexDir) (z : Hex) : Prop :=
  (T.dir z = u + 2 ∧ T.idx z = 1) ∨ (T.dir z = u + 5 ∧ T.idx z = n)

lemma downCell_succ (u : HexDir) (y : Hex) (j : ℕ) :
    T.downCell u y (j + 1) = nbr (T.downCell u y j) u := by
  simp only [downCell, walk_nat_succ, nbr]
  abel

lemma downCell_pred (u : HexDir) (y : Hex) (j : ℕ) :
    nbr (T.downCell u y (j + 1)) (u + 3) = T.downCell u y j := by
  rw [T.downCell_succ]
  exact nbr_nbr_cancel _ (opp_eq_add_three u).symm

lemma downCell_zero (u : HexDir) (y : Hex) : T.downCell u y 0 = nbr (T.head y) (u + 2) := by
  simp [downCell, walk]

lemma downCell_walk (u : HexDir) (y : Hex) (j : ℕ) (k : ℤ) (l : ℕ) (h : (j : ℤ) + k = (l : ℤ)) :
    walk (T.downCell u y j) u k = T.downCell u y l := by
  simp only [downCell, walk, nbr, ← h, add_smul]
  abel

/-- The cells of the row below a stick, as seen from the horizontal stick filling the space
beyond the near end of the stack. -/
lemma downCell_eq_walk (u : HexDir) (y : Hex) (j : ℕ) :
    T.downCell u y j = walk (T.downCell u y 0) u (j : ℤ) :=
  (T.downCell_walk u y 0 (j : ℤ) j (by push_cast; ring)).symm

/-! ### Ascending along the row -/

/-- **The row below a stack, from the horizontal stick beyond the near end to the second
horizontal stack.**  If the `t`-th cell of the row is the far end of a horizontal stick, then
further along the row one reaches the near end of another horizontal stick, and in between the
row consists of ends of left-slanting sticks. -/
lemma bot_row_ascend (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {y : Hex} {u : HexDir} (hdy : T.dir y = u)
    {t : ℕ} (ht : 1 ≤ t) (htn : t + 1 < n)
    (hbase : T.dir (T.downCell u y t) = u ∧ T.idx (T.downCell u y t) = n) :
    ∃ w : ℕ, t < w ∧ w < n ∧ T.dir (T.downCell u y w) = u ∧ T.idx (T.downCell u y w) = 1 ∧
      T.dir (T.downCell u y (w - 1)) = u + 2 ∧ T.idx (T.downCell u y (w - 1)) = 1 ∧
      ∀ j, t < j → j < w → T.SlantEndBelow u (T.downCell u y j) := by
  -- the predecessor of the cell at position `j + 1` in the row is the cell at position `j`
  have hpred : ∀ j : ℕ, nbr (walk (T.head y) u ((j + 1 : ℕ) : ℤ)) (u + 3)
      = walk (T.head y) u (j : ℤ) := by
    intro j
    rw [walk_nat_succ]
    exact nbr_nbr_cancel _ (opp_eq_add_three u).symm
  have W : ∀ k : ℕ,
      (∀ j, t < j → j ≤ t + k → T.SlantEndBelow u (T.downCell u y j) ∧ j + 1 < n) ∨
      (∃ w, t < w ∧ w < n ∧ T.dir (T.downCell u y w) = u ∧ T.idx (T.downCell u y w) = 1 ∧
        T.dir (T.downCell u y (w - 1)) = u + 2 ∧ T.idx (T.downCell u y (w - 1)) = 1 ∧
        ∀ j, t < j → j < w → T.SlantEndBelow u (T.downCell u y j)) := by
    intro k
    induction k with
    | zero => exact Or.inl fun j h1 h2 => absurd h2 (by omega)
    | succ k ih =>
      rcases ih with hall | ⟨w, hw⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · -- the first step, past the far end of the horizontal stick
          obtain ⟨hdp, hip⟩ := T.dir_idx_rowBase hdy (show t + 1 < n by omega)
          have hstep := T.bot_step_tail hv (by omega) hdp (by omega)
            (by rw [hpred t]; exact hbase.1) (by rw [hpred t]; exact hbase.2)
          refine Or.inl fun j h1 h2 => ?_
          have hj : j = t + 1 := by omega
          subst hj
          exact ⟨Or.inr ⟨hstep.2.1, hstep.2.2⟩, by omega⟩
        · -- a further step, past a left-slanting stick
          obtain ⟨hslant, hbound⟩ := hall (t + k) (by omega) (by omega)
          obtain ⟨hdp, hip⟩ := T.dir_idx_rowBase hdy (show t + k + 1 < n by omega)
          rcases hslant with ⟨hd2, hi2⟩ | ⟨hd5, hi5⟩
          · have hstep := T.bot_step_two hv (by omega) hdp (by omega)
              (by rw [hpred (t + k)]; exact hd2) (by rw [hpred (t + k)]; exact hi2)
            rcases hstep with ⟨hd, hi⟩ | ⟨hd, hi, hlt⟩
            · refine Or.inr ⟨t + k + 1, by omega, by omega, hd, hi, ?_, ?_, ?_⟩
              · rw [show t + k + 1 - 1 = t + k from by omega]; exact hd2
              · rw [show t + k + 1 - 1 = t + k from by omega]; exact hi2
              · exact fun j h1 h2 => (hall j h1 (by omega)).1
            · refine Or.inl fun j h1 h2 => ?_
              rcases Nat.lt_or_ge j (t + k + 1) with hlt' | hge
              · exact hall j h1 (by omega)
              · have hj : j = t + k + 1 := by omega
                subst hj
                exact ⟨Or.inl ⟨hd, hi⟩, by omega⟩
          · have hstep := T.bot_step_five hv hdp (by omega)
              (by rw [hpred (t + k)]; exact hd5) (by rw [hpred (t + k)]; exact hi5)
            refine Or.inl fun j h1 h2 => ?_
            rcases Nat.lt_or_ge j (t + k + 1) with hlt' | hge
            · exact hall j h1 (by omega)
            · have hj : j = t + k + 1 := by omega
              subst hj
              exact ⟨hstep.2, by omega⟩
      · exact Or.inr ⟨w, hw⟩
  rcases W n with hall | ⟨w, h1, h2, h3, h4, h5, h6, h7⟩
  · exact absurd (hall (t + n) (by omega) (by omega)).2 (by omega)
  · exact ⟨w, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The second stack below -/

/-- The far end of the horizontal stick filling the space beyond the near end of the stack. -/
lemma downCell_tail_of_frontCorner {y : Hex} {u : HexDir}
    (hdC : T.dir (T.downCell u y 0) = u) :
    T.dir (T.downCell u y (n - T.idx (T.downCell u y 0))) = u ∧
      T.idx (T.downCell u y (n - T.idx (T.downCell u y 0))) = n := by
  have hle := T.idx_le (T.downCell u y 0)
  have hpos := T.idx_pos (T.downCell u y 0)
  have h := T.dir_walk_forward (T.downCell u y 0) (n - T.idx (T.downCell u y 0)) (by omega)
  rw [hdC] at h
  rw [← T.downCell_eq_walk] at h
  exact ⟨h.1, by omega⟩

/-- The stick whose near end is the `w`-th cell of the row below the stack lies in a left-leaning
stack. -/
lemma isLeftLeaningStack_downCell (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {y : Hex} {u : HexDir} {w : ℕ}
    (hw : 1 ≤ w) (hdw : T.dir (T.downCell u y w) = u) (hiw : T.idx (T.downCell u y w) = 1)
    (hd2 : T.dir (T.downCell u y (w - 1)) = u + 2) (hi2 : T.idx (T.downCell u y (w - 1)) = 1) :
    T.IsLeftLeaningStack (T.downCell u y w) := by
  have hw1 : w - 1 + 1 = w := by omega
  have hp4 : nbr (T.downCell u y (w - 1)) (T.dir (T.downCell u y (w - 1)) + 4)
      = T.downCell u y w := by
    rw [hd2, add_two_four u]
    conv_rhs => rw [← hw1]
    rw [T.downCell_succ]
  have hend : T.EndsAt (nbr (T.downCell u y (w - 1)) (T.dir (T.downCell u y (w - 1)) + 4))
      (T.dir (T.downCell u y (w - 1)) + 1) := by
    rw [hp4, hd2, (by decide : ∀ a : HexDir, a + 2 + 1 = a + 3)]
    exact Or.inr ⟨by rw [hdw, opp_add_three], hiw⟩
  have hpair := T.leansLeft_of_endsAt_corner hv hn (p := T.downCell u y (w - 1))
    (by rw [hi2]; omega) hend
  rw [hp4] at hpair
  exact ⟨T.downCell u y w, _, T.sameStack_refl _, hpair⟩

/-- The cells of the row after the `w`-th one all belong to the stick whose near end it is. -/
lemma downCell_mem_stickOf_of_ge {y : Hex} {u : HexDir} {w j : ℕ}
    (hdw : T.dir (T.downCell u y w) = u) (hiw : T.idx (T.downCell u y w) = 1)
    (hjw : w ≤ j) (hj : j < w + n) : T.downCell u y j ∈ T.stickOf (T.downCell u y w) := by
  rw [T.mem_stickOf_iff]
  refine ⟨j - w, by omega, ?_⟩
  rw [cellOfStick, head, hdw, hiw]
  simp only [Nat.cast_one, sub_self, neg_zero, walk]
  simp only [zero_smul, add_zero]
  exact T.downCell_walk u y w _ j (by omega)

/-- The second stack below a left-leaning stack is a different stack. -/
lemma not_sameStack_downCell (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c y : Hex} {u : HexDir} {w : ℕ}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hy : T.SameStack c y) (hw : 1 ≤ w)
    (hdw : T.dir (T.downCell u y w) = u) (hiw : T.idx (T.downCell u y w) = 1) :
    ¬ T.SameStack c (T.downCell u y w) := by
  intro hsame
  have h0n : 0 < n := by omega
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hy, hu]
  have hne3 : u ≠ u + 3 := (by decide : ∀ a : HexDir, a ≠ a + 3) u
  have hax0 : SameAxis (u + 3) (T.dir c) := Or.inr (by rw [hu, opp_add_three])
  have hmem := (T.frontCell_mem_of_sameStack hv h0n hax0 hsame).2
  have hmemy := (T.frontCell_mem_of_sameStack hv h0n hax0 hy).2
  have hfy : T.frontCell (u + 3) y = nbr (T.head y) (u + 3) := by
    rw [frontCell, endCell, if_neg (by rw [hdy]; exact hne3)]
  have hfw : T.frontCell (u + 3) (T.downCell u y w) = T.downCell u y (w - 1) := by
    rw [frontCell, endCell, if_neg (by rw [hdw]; exact hne3), head, hdw, hiw]
    simp only [Nat.cast_one, sub_self, neg_zero, walk, zero_smul, add_zero]
    rw [show w = (w - 1) + 1 from by omega, T.downCell_succ]
    exact nbr_nbr_cancel _ (opp_eq_add_three u).symm
  have hdE : T.dir (T.frontCell (u + 3) c) = u + 2 := by
    have h1 := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl c)).2
    rw [hu, opp_eq_add_three] at h1
    rw [frontCell, endCell, if_neg (by rw [hu]; exact hne3)]
    exact h1
  rw [hfy] at hmemy
  rw [hfw] at hmem
  obtain ⟨k, hk⟩ := T.exists_walk_of_mem_stickOf hmem hmemy
  rw [hdE] at hk
  have hkey : ((w : ℤ)) • u.vec = (k - 1) • (u + 2).vec := by
    simp only [downCell, walk, nbr] at hk
    rw [show ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 from by omega] at hk
    have hvec : (u + 3).vec = -u.vec := vec_add_three u
    rw [hvec] at hk
    linear_combination (norm := module) hk
  obtain ⟨h1, -⟩ := smul_vec_eq_smul_vec ((by decide : ∀ a : HexDir, a ≠ a + 2) u)
    (by rw [opp_add_two]; exact (by decide : ∀ a : HexDir, a ≠ a + 5) u) hkey
  omega

/-- The second stack below a left-leaning stack is different from the first one. -/
lemma not_sameStack_frontCorner_downCell (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {y : Hex} {u : HexDir}
    {w t : ℕ} (hLC : T.IsLeftLeaningStack (T.downCell u y 0))
    (hdC : T.dir (T.downCell u y 0) = u) (ht : t = n - T.idx (T.downCell u y 0)) (htn : t < n)
    (hw : 1 ≤ w)
    (hdw : T.dir (T.downCell u y w) = u) (hiw : T.idx (T.downCell u y w) = 1) :
    ¬ T.SameStack (T.downCell u y 0) (T.downCell u y w) := by
  intro hsame
  have h0n : 0 < n := by omega
  have hax0 : SameAxis u (T.dir (T.downCell u y 0)) := Or.inl hdC
  have hmem := (T.frontCell_mem_of_sameStack hv h0n hax0 hsame).2
  have hle := T.idx_le (T.downCell u y 0)
  have hpos := T.idx_pos (T.downCell u y 0)
  -- the cell beyond the far end of the first stick
  have hfC : T.frontCell u (T.downCell u y 0) = T.downCell u y (t + 1) := by
    rw [frontCell, endCell, if_pos hdC, T.tail_eq_walk h0n, hdC, nbr_eq_walk_one, walk_walk,
      T.downCell_walk u y 0 _ (t + 1) (by rw [ht]; omega)]
  -- the cell beyond the far end of the second stick
  have hfw : T.frontCell u (T.downCell u y w) = T.downCell u y (w + n) := by
    rw [frontCell, endCell, if_pos hdw, T.tail_eq_walk h0n, hdw, hiw, nbr_eq_walk_one, walk_walk,
      T.downCell_walk u y w _ (w + n) (by push_cast; ring)]
  have hdF : T.dir (T.frontCell u (T.downCell u y 0)) = u + 5 := by
    have h1 := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hLC (T.sameStack_refl _)).1
    rw [hdC] at h1
    rw [frontCell, endCell, if_pos hdC]
    exact h1
  rw [hfw, hfC] at hmem
  rw [hfC] at hdF
  obtain ⟨k, hk⟩ := T.exists_walk_of_mem_stickOf hmem (T.self_mem_stickOf _)
  rw [hdF] at hk
  have hkey : (((w : ℤ) + n) - (t + 1)) • u.vec = k • (u + 5).vec := by
    simp only [downCell, walk, nbr] at hk
    push_cast at hk
    linear_combination (norm := module) hk
  obtain ⟨h1, -⟩ := smul_vec_eq_smul_vec ((by decide : ∀ a : HexDir, a ≠ a + 5) u)
    (by rw [opp_add_five]; exact (by decide : ∀ a : HexDir, a ≠ a + 2) u) hkey
  omega

/-- **Every left-leaning stack has (at least) two left-leaning stacks below it.**  Mirror image
of `StickTiling.exists_two_stackAbove`: a left-leaning stack of horizontal sticks of direction
`u` has, on its front side, two *different* left-leaning stacks of horizontal sticks of the same
direction. -/
theorem exists_two_stackBelow (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ b₁ b₂ : Hex, T.dir b₁ = u ∧ T.IsLeftLeaningStack b₁ ∧ T.StackBelow u c b₁ ∧
      T.dir b₂ = u ∧ T.IsLeftLeaningStack b₂ ∧ T.StackBelow u c b₂ ∧ ¬ T.SameStack b₁ b₂ := by
  have h0n : 0 < n := by omega
  obtain ⟨y, hy, hne⟩ := T.exists_frontCorner_not_sameStack hv (by omega) hL hu
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hy, hu]
  obtain ⟨hdC, hcase⟩ := T.dir_frontCorner_beyond_head hv (by omega) hL hu hy
  rw [← T.downCell_zero u y] at hdC hne hcase
  obtain ⟨hi1, hin⟩ : 1 < T.idx (T.downCell u y 0) ∧ T.idx (T.downCell u y 0) < n := by
    rcases hcase with ⟨-, hsame⟩ | h
    · exact absurd hsame hne
    · exact h
  have hLC : T.IsLeftLeaningStack (T.downCell u y 0) := by
    rcases T.isLeftLeaningStack_frontCorner hv hn hL hu hy with h | h
    · rw [← T.downCell_zero u y] at h
      exact absurd h hne
    · rw [← T.downCell_zero u y] at h
      exact h
  -- the far end of the first stick below, and the row beyond it
  obtain ⟨hdt, hit⟩ := T.downCell_tail_of_frontCorner hdC
  obtain ⟨w, hw1, hwn, hdw, hiw, hd2, hi2, hslant⟩ := T.bot_row_ascend hv (by omega) hdy
    (t := n - T.idx (T.downCell u y 0)) (by omega) (by omega) ⟨hdt, hit⟩
  refine ⟨T.downCell u y 0, T.downCell u y w, hdC, hLC, ⟨hne, T.head y, ?_, ?_⟩, hdw,
    T.isLeftLeaningStack_downCell hv (by omega) (by omega) hdw hiw hd2 hi2,
    ⟨T.not_sameStack_downCell hv (by omega) hL hu hy (by omega) hdw hiw,
      walk (T.head y) u (w : ℤ), ?_, ?_⟩,
    T.not_sameStack_frontCorner_downCell hv (by omega) hLC hdC rfl (by omega) (by omega) hdw hiw⟩
  · exact SameStack.trans T hy
      (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.head_mem_stickOf y)).symm)
  · exact Or.inr (by rw [← T.downCell_zero u y]; exact T.sameStack_refl _)
  · refine SameStack.trans T hy (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem ?_).symm)
    rw [T.mem_stickOf_iff]
    exact ⟨w, by omega, by rw [cellOfStick, hdy]⟩
  · exact Or.inr (T.sameStack_refl _)

end StickTiling

end StickPolyhex
