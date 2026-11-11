import Tiling.Proofs.StepHole

/-!
# The grid of horizontal stacks

Once every cell of the tiling is known to be a weave cell, the remaining conditions of the weave
pattern concern the way the horizontal stacks are arranged: each of them has exactly two
horizontal stacks above it and exactly two below it, adjacent horizontal stacks overlap at a
concave corner, and the four horizontal stacks of a grid cell enclose a vertical stack with at
least two sticks.

Throughout, `hcov` records that every cell of the tiling is a weave cell for the orientation
`u`, which is the conclusion of `StickTiling.exists_weaveCell_all`.  It is used to know that
every horizontal stick lies in a left-leaning stack, which is what pins down the stacks lying
above and below a given one.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Horizontal and left-slanting weave cells -/

/-- A horizontal stick of direction `u` lies in a left-leaning stack. -/
lemma isLeftLeaningStack_of_weaveCell {u : HexDir} {z : Hex} (h : T.WeaveCell u z)
    (hd : T.dir z = u) : T.IsLeftLeaningStack z := by
  rcases h with ⟨-, hL⟩ | ⟨hs, -⟩
  · exact hL
  · exfalso
    rcases hs with h2 | h5
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hd.symm.trans h2)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hd.symm.trans h5)

/-- A left-slanting stick lies in a right-leaning stack. -/
lemma isRightLeaningStack_of_weaveCell {u : HexDir} {z : Hex} (h : T.WeaveCell u z)
    (hs : T.SlantsLeft u z) : T.IsRightLeaningStack z := by
  rcases h with ⟨hd, -⟩ | ⟨-, hR⟩
  · exfalso
    rcases hs with h2 | h5
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hd.symm.trans h2)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hd.symm.trans h5)
  · exact hR

/-! ### The cells adjacent to a stack in the upward and downward directions -/

/-- The cells adjacent to a left-leaning stack in the two upward directions `u + 4` and `u + 5`:
such a cell belongs to the stack itself, to the stick flanking the near ends of its sticks, to
the row above its topmost stick, or it is the corner cell diagonally above the near end of that
stick.  In particular it never lies in the row below the stack. -/
lemma up_nbr_classification (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x p : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (htop : nbr (T.tail x) u = T.tail (nbr (T.tail c) u)) (hp : T.SameStack c p) {e : HexDir}
    (he : e = u + 4 ∨ e = u + 5) :
    T.SameStack c (nbr p e) ∨
      nbr p e ∈ T.stickOf (nbr (T.head c) (u + 3)) ∨
      (∃ j, j < n ∧ nbr p e = T.upCell u x j) ∨
      nbr p e = nbr (T.head x) (u + 4) := by
  rcases he with rfl | rfl
  · rw [← nbr_nbr_of_vec p (vec_five_three u)]
    rcases T.up_classification hv hn hL hu hx htop hp with h | ⟨j, hj, hjeq⟩
    · rcases T.nbr_opp_dir_classification hv hn hL hu h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rw [hjeq]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [T.upCell_zero]
        exact nbr_nbr_of_vec (T.head x) (vec_five_three u)
      · refine Or.inr (Or.inr (Or.inl ⟨j - 1, by omega, ?_⟩))
        conv_lhs => rw [show j = (j - 1) + 1 from by omega]
        exact T.upCell_pred u x (j - 1)
  · rcases T.up_classification hv hn hL hu hx htop hp with h | ⟨j, hj, hjeq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨j, hj, hjeq⟩))

/-- The cells adjacent to a left-leaning stack in the two downward directions `u + 1` and
`u + 2`: such a cell belongs to the stack itself, to the stick flanking the far ends of its
sticks, or to the row below its bottommost stick. -/
lemma down_nbr_classification (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c y p : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hy : T.SameStack c y)
    (hbot : nbr (T.tail y) u = T.head (nbr (T.tail c) u)) (hp : T.SameStack c p) {e : HexDir}
    (he : e = u + 1 ∨ e = u + 2) :
    T.SameStack c (nbr p e) ∨
      nbr p e ∈ T.stickOf (nbr (T.tail c) u) ∨
      (∃ j, j ≤ n ∧ nbr p e = T.downCell u y j) := by
  rcases he with rfl | rfl
  · rw [← nbr_nbr_of_vec p ((by decide : ∀ a : HexDir, (a + 2).vec + a.vec = (a + 1).vec) u)]
    rcases T.down_classification hv hn hL hu hy hbot hp with h | ⟨j, hj, hjeq⟩
    · rcases T.nbr_dir_classification hv hn hL hu h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · refine Or.inr (Or.inr ⟨j + 1, by omega, ?_⟩)
      rw [hjeq, T.downCell_succ]
  · rcases T.down_classification hv hn hL hu hy hbot hp with h | ⟨j, hj, hjeq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨j, by omega, hjeq⟩)

/-! ### The horizontal stacks above a horizontal stack -/

/-- **Every horizontal stack above a left-leaning stack is one of the two stacks produced by the
analysis of the row above its topmost stick.**  A cell adjacent to the stack in one of the two
upward directions lies in the stack itself, on the stick flanking the near ends of its sticks,
in the row above its topmost stick, or on the corner cell beyond the near end of that stick;
since a horizontal stick lies in a left-leaning stack, the left-slanting possibilities are
excluded. -/
lemma stackAbove_classification (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir}
    (hcov : ∀ z, T.WeaveCell u z) {c x : Hex} {s : ℕ}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (htop : nbr (T.tail x) u = T.tail (nbr (T.tail c) u))
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n) (hs2 : s + 2 ≤ n)
    (hrow : ∀ j, s < j → j < n → T.SlantEndAbove u (T.upCell u x j) ∨
      T.upCell u x j ∈ T.stickOf (nbr (T.tail x) (u + 5)))
    {a : Hex} (hda : T.dir a = u) (habove : T.StackAbove u c a) :
    T.SameStack a (nbr (T.tail x) (u + 5)) ∨ T.SameStack a (T.upCell u x s) := by
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have hbelowRow : ∀ j, j < n → T.dir (nbr (T.upCell u x j) (u + 2)) = u := by
    intro j hj
    rw [show nbr (T.upCell u x j) (u + 2) = walk (T.head x) u (j : ℤ) from by
      rw [upCell]; exact nbr_nbr_cancel _ (opp_add_five u).symm]
    exact (T.dir_idx_rowBase hdx hj).1
  obtain ⟨hnea, p, hp, hcase⟩ := habove
  have hLa : T.IsLeftLeaningStack a := T.isLeftLeaningStack_of_weaveCell (hcov a) hda
  obtain ⟨e, he, hae⟩ : ∃ e, (e = u + 4 ∨ e = u + 5) ∧ T.SameStack a (nbr p e) := by
    rcases hcase with h | h
    · exact ⟨u + 4, Or.inl rfl, h⟩
    · exact ⟨u + 5, Or.inr rfl, h⟩
  rcases T.up_nbr_classification hv (by omega) hL hu hx htop hp he with
    hsame | hmemE | ⟨j, hj, hjeq⟩ | hcorner
  · exact absurd (SameStack.trans T hsame (SameStack.symm T hae)) hnea
  · exact absurd (T.isLeftLeaningStack_of_sameStack hLa
      (SameStack.trans T hae (T.sameStack_of_mem_stickOf hmemE)))
      (T.not_isLeftLeaningStack_frontFlank hv (by omega) hL hu hx htop hds his hs2)
  · rw [hjeq] at hae
    rcases Nat.lt_or_ge s j with hjs | hjs
    · rcases hrow j hjs hj with hslant | hmem
      · exact absurd (T.isLeftLeaningStack_of_sameStack hLa hae)
          (T.not_isLeftLeaningStack_slantEndAbove hv (by omega) hslant (hbelowRow j hj))
      · exact Or.inl (SameStack.trans T hae (T.sameStack_of_mem_stickOf hmem))
    · exact Or.inr (SameStack.trans T hae (T.sameStack_of_mem_stickOf
        (T.upCell_mem_stickOf_of_le hds his (by omega) hjs)))
  · rw [hcorner] at hae
    exact Or.inr (SameStack.trans T hae (T.sameStack_of_mem_stickOf
      (T.backCorner_head_mem_stickOf hds his hs2)))

/-! ### Two stacks above and two stacks below -/

/-- **Each horizontal stack has exactly two horizontal stacks above it and exactly two below
it.**  The four stacks are the ones produced by
`StickTiling.exists_four_leftLeaningStack_neighbours`; that every *horizontal* stack lying above
or below `c` is one of them uses that every horizontal stick lies in a left-leaning stack. -/
theorem two_above_two_below_of_weaveCell (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir}
    (hcov : ∀ z, T.WeaveCell u z) {c : Hex} (hu : T.dir c = u) :
    (∃ a₁ a₂, T.dir a₁ = u ∧ T.dir a₂ = u ∧ ¬ T.SameStack a₁ a₂ ∧
        T.StackAbove u c a₁ ∧ T.StackAbove u c a₂ ∧
        ∀ a, T.dir a = u → T.StackAbove u c a → T.SameStack a a₁ ∨ T.SameStack a a₂) ∧
      (∃ b₁ b₂, T.dir b₁ = u ∧ T.dir b₂ = u ∧ ¬ T.SameStack b₁ b₂ ∧
        T.StackBelow u c b₁ ∧ T.StackBelow u c b₂ ∧
        ∀ b, T.dir b = u → T.StackBelow u c b → T.SameStack b b₁ ∨ T.SameStack b b₂) := by
  have h0n : 0 < n := by omega
  have hL : T.IsLeftLeaningStack c := T.isLeftLeaningStack_of_weaveCell (hcov c) hu
  -- ### the topmost stick and the row above it
  obtain ⟨x, hx, hneA⟩ := T.exists_backCorner_not_sameStack hv (by omega) hL hu
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have htop := T.tail_nbr_eq_tail_flank hv (by omega) hL hu hx hneA
  obtain ⟨hdA, hcaseA⟩ := T.dir_backCorner_beyond_tail hv (by omega) hL hu hx
  obtain ⟨hi1, hin⟩ :
      1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n := by
    rcases hcaseA with ⟨-, hsame⟩ | h
    · exact absurd hsame hneA
    · exact h
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv (by omega) hL hu hx hi1 hin
  have hbelowRow : ∀ j, j < n → T.dir (nbr (T.upCell u x j) (u + 2)) = u := by
    intro j hj
    rw [show nbr (T.upCell u x j) (u + 2) = walk (T.head x) u (j : ℤ) from by
      rw [upCell]; exact nbr_nbr_cancel _ (opp_add_five u).symm]
    exact (T.dir_idx_rowBase hdx hj).1
  -- ### the bottommost stick and the row below it
  obtain ⟨y, hy, hneC⟩ := T.exists_frontCorner_not_sameStack hv (by omega) hL hu
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hy, hu]
  have hbot := T.tail_nbr_eq_head_flank hv (by omega) hL hu hy hneC
  obtain ⟨hdC, hcaseC⟩ := T.dir_frontCorner_beyond_head hv (by omega) hL hu hy
  rw [← T.downCell_zero u y] at hdC hneC hcaseC
  obtain ⟨hiC1, hiCn⟩ : 1 < T.idx (T.downCell u y 0) ∧ T.idx (T.downCell u y 0) < n := by
    rcases hcaseC with ⟨-, hsame⟩ | h
    · exact absurd hsame hneC
    · exact h
  have hLC : T.IsLeftLeaningStack (T.downCell u y 0) := by
    rcases T.isLeftLeaningStack_frontCorner hv (by omega) hL hu hy with h | h
    · rw [← T.downCell_zero u y] at h
      exact absurd h hneC
    · rw [← T.downCell_zero u y] at h
      exact h
  obtain ⟨hdt, hit⟩ := T.downCell_tail_of_frontCorner hdC
  obtain ⟨w, hw1, hwn, hdw, hiw, hd2', hi2', hslantB⟩ := T.bot_row_ascend hv (by omega) hdy
    (t := n - T.idx (T.downCell u y 0)) (by omega) (by omega) ⟨hdt, hit⟩
  have haboveRow : ∀ j, j < n → T.dir (nbr (T.downCell u y j) (u + 5)) = u := by
    intro j hj
    rw [show nbr (T.downCell u y j) (u + 5) = walk (T.head y) u (j : ℤ) from by
      rw [downCell]; exact nbr_nbr_cancel _ (opp_add_two u).symm]
    exact (T.dir_idx_rowBase hdy hj).1
  -- ### the four stacks
  have hLA : T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)) := by
    rcases T.isLeftLeaningStack_backCorner hv (by omega) hL hu hx with h | h
    · exact absurd h hneA
    · exact h
  have hne12 : ¬ T.SameStack (nbr (T.tail x) (u + 5)) (T.upCell u x s) :=
    T.not_sameStack_backCorner_upCell hv (by omega) hLA hdA hdx hds his hs2
  have hne34 : ¬ T.SameStack (T.downCell u y 0) (T.downCell u y w) :=
    T.not_sameStack_frontCorner_downCell hv (by omega) hLC hdC rfl (by omega) (by omega) hdw hiw
  have hAbove1 : T.StackAbove u c (nbr (T.tail x) (u + 5)) :=
    ⟨hneA, T.tail x, SameStack.trans T hx (T.sameStack_of_stickOf_eq
      (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n x)).symm), Or.inr (T.sameStack_refl _)⟩
  have hAbove2 : T.StackAbove u c (T.upCell u x s) := by
    refine ⟨T.not_sameStack_upCell hv (by omega) hL hu hx hds his hs2, T.head x,
      SameStack.trans T hx (T.sameStack_of_stickOf_eq
        (T.stickOf_eq_of_mem (T.head_mem_stickOf x)).symm), Or.inr ?_⟩
    rw [← T.upCell_zero]
    exact (T.sameStack_of_mem_stickOf
      (T.upCell_mem_stickOf_of_le hds his (by omega) (Nat.zero_le s))).symm
  have hBelow1 : T.StackBelow u c (T.downCell u y 0) := by
    refine ⟨hneC, T.head y, SameStack.trans T hy (T.sameStack_of_stickOf_eq
      (T.stickOf_eq_of_mem (T.head_mem_stickOf y)).symm), Or.inr ?_⟩
    rw [← T.downCell_zero u y]
    exact T.sameStack_refl _
  have hBelow2 : T.StackBelow u c (T.downCell u y w) := by
    refine ⟨T.not_sameStack_downCell hv (by omega) hL hu hy (by omega) hdw hiw,
      walk (T.head y) u (w : ℤ), ?_, Or.inr (T.sameStack_refl _)⟩
    refine SameStack.trans T hy (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem ?_).symm)
    rw [T.mem_stickOf_iff]
    exact ⟨w, by omega, by rw [cellOfStick, hdy]⟩
  refine ⟨⟨nbr (T.tail x) (u + 5), T.upCell u x s, hdA, hds, hne12, hAbove1, hAbove2, ?_⟩,
    ⟨T.downCell u y 0, T.downCell u y w, hdC, hdw, hne34, hBelow1, hBelow2, ?_⟩⟩
  · exact fun a hda habove =>
      T.stackAbove_classification hv hn hcov hL hu hx htop hds his hs2 hrow hda habove
  · -- every horizontal stack below `c` is one of the two
    intro b hdb hbelow
    obtain ⟨hneb, p, hp, hcase⟩ := hbelow
    have hLb : T.IsLeftLeaningStack b := T.isLeftLeaningStack_of_weaveCell (hcov b) hdb
    obtain ⟨e, he, hbe⟩ : ∃ e, (e = u + 1 ∨ e = u + 2) ∧ T.SameStack b (nbr p e) := by
      rcases hcase with h | h
      · exact ⟨u + 1, Or.inl rfl, h⟩
      · exact ⟨u + 2, Or.inr rfl, h⟩
    rcases T.down_nbr_classification hv (by omega) hL hu hy hbot hp he with
      hsame | hmemF | ⟨j, hj, hjeq⟩
    · exact absurd (SameStack.trans T hsame (SameStack.symm T hbe)) hneb
    · exact absurd (T.isLeftLeaningStack_of_sameStack hLb
        (SameStack.trans T hbe (T.sameStack_of_mem_stickOf hmemF)))
        (T.not_isLeftLeaningStack_flank hv (by omega) hL hu hx htop hin)
    · rw [hjeq] at hbe
      rcases Nat.lt_or_ge (n - T.idx (T.downCell u y 0)) j with hjt | hjt
      · rcases Nat.lt_or_ge j w with hjw | hjw
        · exact absurd (T.isLeftLeaningStack_of_sameStack hLb hbe)
            (T.not_isLeftLeaningStack_slantEndBelow hv (by omega) (hslantB j hjt hjw)
              (haboveRow j (by omega)))
        · exact Or.inr (SameStack.trans T hbe (T.sameStack_of_mem_stickOf
            (T.downCell_mem_stickOf_of_ge hdw hiw hjw (by omega))))
      · exact Or.inl (SameStack.trans T hbe
          (T.sameStack_of_mem_stickOf (T.downCell_mem_stickOf_of_le hdC hjt)))

/-! ### Overlapping stacks -/

/-- **Adjacent horizontal stacks overlap by at least one concave corner.** -/
theorem overlap_of_weaveCell (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir}
    (hcov : ∀ z, T.WeaveCell u z) {c c' : Hex} (hu : T.dir c = u) (hu' : T.dir c' = u)
    (habove : T.StackAbove u c c') :
    ∃ x, T.SameStack c x ∧ T.idx x < n ∧ T.SameStack c' (nbr x (u + 5)) := by
  have h0n : 0 < n := by omega
  have hL : T.IsLeftLeaningStack c := T.isLeftLeaningStack_of_weaveCell (hcov c) hu
  obtain ⟨x, hx, hneA⟩ := T.exists_backCorner_not_sameStack hv (by omega) hL hu
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have htop := T.tail_nbr_eq_tail_flank hv (by omega) hL hu hx hneA
  obtain ⟨hdA, hcaseA⟩ := T.dir_backCorner_beyond_tail hv (by omega) hL hu hx
  obtain ⟨hi1, hin⟩ :
      1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n := by
    rcases hcaseA with ⟨-, hsame⟩ | h
    · exact absurd hsame hneA
    · exact h
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv (by omega) hL hu hx hi1 hin
  -- the cells of the topmost stick, in the form used by the row analysis
  have hrowcell : ∀ j, j < n → T.SameStack c (walk (T.head x) u (j : ℤ)) ∧
      T.idx (walk (T.head x) u (j : ℤ)) = j + 1 := by
    intro j hj
    refine ⟨?_, (T.dir_idx_rowBase hdx hj).2⟩
    have hmemx : walk (T.head x) u (j : ℤ) ∈ T.stickOf x := by
      rw [T.mem_stickOf_iff]
      exact ⟨j, hj, by rw [cellOfStick, hdx]⟩
    exact SameStack.trans T hx (SameStack.symm T (T.sameStack_of_mem_stickOf hmemx))
  -- `c'` is one of the two stacks above `c`
  rcases T.stackAbove_classification hv hn hcov hL hu hx htop hds his hs2 hrow hu' habove with
    hA | hB
  · -- the stack filling the space `A`: use the cell just before the far end of the topmost stick
    refine ⟨walk (T.head x) u ((n - 2 : ℕ) : ℤ), (hrowcell (n - 2) (by omega)).1, ?_, ?_⟩
    · rw [(hrowcell (n - 2) (by omega)).2]
      omega
    · have hmem : T.upCell u x (n - 2) ∈ T.stickOf (nbr (T.tail x) (u + 5)) :=
        T.upCell_mem_stickOf_backCorner h0n hdA hdx (by omega) (by omega)
      exact SameStack.trans T hA (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))
  · -- the second horizontal stack above: use the cell of the topmost stick below its far end
    refine ⟨walk (T.head x) u (s : ℤ), (hrowcell s (by omega)).1, ?_, hB⟩
    rw [(hrowcell s (by omega)).2]
    omega

/-! ### Transporting the relations between stacks -/

/-- Lying above a stack only depends on the stack. -/
lemma stackAbove_of_sameStack {u : HexDir} {c c' a : Hex} (hcc : T.SameStack c c')
    (h : T.StackAbove u c a) : T.StackAbove u c' a := by
  obtain ⟨hne, z, hz, hcase⟩ := h
  exact ⟨fun hs => hne (SameStack.trans T hcc hs), z,
    SameStack.trans T (SameStack.symm T hcc) hz, hcase⟩

/-- Adjacency of stacks only depends on the stacks. -/
lemma stackAdjacent_of_sameStack {v a a' : Hex} (haa : T.SameStack a a')
    (h : T.StackAdjacent v a) : T.StackAdjacent v a' := by
  obtain ⟨hne, z, e, hz, hae⟩ := h
  exact ⟨fun hs => hne (SameStack.trans T hs (SameStack.symm T haa)), z, e, hz,
    SameStack.trans T (SameStack.symm T haa) hae⟩

/-- A stack of left-slanting sticks is not a stack of horizontal sticks. -/
lemma not_sameStack_of_dir_ne (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {u : HexDir} {q z : Hex}
    (hL : T.IsLeftLeaningStack q) (hdq : T.dir q = u) (hdz : T.dir z ≠ u) :
    ¬ T.SameStack z q := by
  intro h
  exact hdz (by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL (SameStack.symm T h), hdq])

/-- Two neighbouring horizontal cells of direction `u`, the first one in a left-leaning stack,
lie in the same stack. -/
lemma sameStack_nbr_of_dir_eq (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {u : HexDir} {g : Hex}
    (hL : T.IsLeftLeaningStack g) (hd : T.dir g = u) (hd' : T.dir (nbr g u) = u) :
    T.SameStack g (nbr g u) := by
  have h0n : 0 < n := by omega
  by_cases hi : T.idx g = n
  · exfalso
    have htail : T.tail g = g := (T.eq_tail_of_mem_of_idx_eq h0n (T.self_mem_stickOf g) hi).symm
    have hf := T.dir_flank hv hn hL hd
    rw [htail] at hf
    exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hd'.symm.trans hf)
  · have hmem := T.nbr_dir_mem_stickOf g (lt_of_le_of_ne (T.idx_le g) hi)
    rw [hd] at hmem
    exact SameStack.symm T (T.sameStack_of_mem_stickOf hmem)

/-! ### The grid cells -/

/-- **The grid cell above a horizontal stack.**  Together with the two horizontal stacks `A` and
`B` above `c`, produced by the analysis of the row above its topmost stick, there is a fourth
horizontal stack `a₃` lying above both, and the vertical stack `v` filling the space between
them: it consists of at least two left-slanting sticks and is adjacent to all four horizontal
stacks.

The stack `a₃` is the one met by the cells just above the upper ends of the sticks of `v`; that
it lies above `A` is the statement that it fills the corner beyond the near end of the topmost
stick of `A`, and that it lies above `B` follows because the sticks of `v` flank the far ends of
the sticks of `B`. -/
lemma grid_cell_core (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} (hcov : ∀ z, T.WeaveCell u z)
    {c : Hex} (hu : T.dir c = u) :
    ∃ a₃ v A B, (∀ a, T.dir a = u → T.StackAbove u c a → T.SameStack a A ∨ T.SameStack a B) ∧
      T.dir a₃ = u ∧ T.StackAbove u A a₃ ∧ T.StackAbove u B a₃ ∧
      T.SlantsLeft u v ∧ 2 ≤ T.stackHeight v ∧ T.StackAdjacent v c ∧ T.StackAdjacent v A ∧
      T.StackAdjacent v B ∧ T.StackAdjacent v a₃ := by
  have h0n : 0 < n := by omega
  have hL : T.IsLeftLeaningStack c := T.isLeftLeaningStack_of_weaveCell (hcov c) hu
  -- ### the topmost stick and the row above it
  obtain ⟨x, hx, hneA⟩ := T.exists_backCorner_not_sameStack hv (by omega) hL hu
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have htop := T.tail_nbr_eq_tail_flank hv (by omega) hL hu hx hneA
  obtain ⟨hdA, hcaseA⟩ := T.dir_backCorner_beyond_tail hv (by omega) hL hu hx
  obtain ⟨hi1, hin⟩ :
      1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n := by
    rcases hcaseA with ⟨-, hsame⟩ | h
    · exact absurd hsame hneA
    · exact h
  have hLA : T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)) := by
    rcases T.isLeftLeaningStack_backCorner hv (by omega) hL hu hx with h | h
    · exact absurd h hneA
    · exact h
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv (by omega) hL hu hx hi1 hin
  have hLU : T.IsLeftLeaningStack (T.upCell u x s) :=
    T.isLeftLeaningStack_upCell hv (by omega) hds his hd5 hi5
  obtain ⟨hdm, him⟩ := T.top_row_base hv (by omega) hL hu hx hi1 hin
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = n - T.idx (nbr (T.tail x) (u + 5)) - 1 := ⟨_, rfl⟩
  rw [← hmdef] at hdm him
  have hle : T.idx (nbr (T.tail x) (u + 5)) ≤ n := T.idx_le _
  have hmn : m < n := by omega
  -- ### the left-slanting sticks of the vertical stack
  have hnotslant' : ∀ k, k < n → m < k → ¬ T.SlantEndAbove u (T.upCell u x k) := by
    intro k hkn hk hsl
    have hmemk : T.upCell u x k ∈ T.stickOf (nbr (T.tail x) (u + 5)) :=
      T.upCell_mem_stickOf_backCorner h0n hdA hdx (by omega) hkn
    have hdk : T.dir (T.upCell u x k) = u := by rw [T.dir_of_mem_stickOf hmemk, hdA]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  have hslantrun : ∀ k, s < k → k ≤ m → T.SlantEndAbove u (T.upCell u x k) := by
    intro k hk hkm
    rcases hrow k hk (by omega) with hsl | hmemk
    · exact hsl
    · have hge := T.le_of_mem_stickOf_backCorner h0n hdA hdx hle hmemk
      omega
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
  -- ### the cells just above the upper ends of those sticks
  have hGdata : ∀ k, s < k → k ≤ m →
      T.dir (walk (T.upCell u x k) (u + 5) (n : ℤ)) = u ∧
        T.IsLeftLeaningStack (walk (T.upCell u x k) (u + 5) (n : ℤ)) := by
    intro k hsk hkm
    have hdp : T.dir (walk (T.head x) u (k : ℤ)) = u := (T.dir_idx_rowBase hdx (by omega)).1
    have hmemx : walk (T.head x) u (k : ℤ) ∈ T.stickOf x := by
      rw [T.mem_stickOf_iff]
      exact ⟨k, by omega, by rw [cellOfStick, hdx]⟩
    have hLp : T.IsLeftLeaningStack (walk (T.head x) u (k : ℤ)) :=
      T.isLeftLeaningStack_of_sameStack hL
        (SameStack.trans T hx (SameStack.symm T (T.sameStack_of_mem_stickOf hmemx)))
    exact T.dir_isLeftLeaning_above_topCell hv hn hdp hLp (hslantrun k hsk hkm)
  -- ### the sticks of the vertical stack lie in one stack, and so do the cells above them
  have hvchain : ∀ d k, k = s + 1 + d → k ≤ m →
      T.SameStack (T.upCell u x (s + 1)) (T.upCell u x k) := by
    intro d
    induction d with
    | zero =>
      intro k hk _
      rw [show k = s + 1 from by omega]
      exact T.sameStack_refl _
    | succ d ih =>
      intro k hk hkm
      have hprev := ih (k - 1) (by omega) (by omega)
      have hstep : nbr (T.upCell u x (k - 1)) u = T.upCell u x k := by
        rw [← T.upCell_succ, show k - 1 + 1 = k from by omega]
      have hst := T.stackedBy_of_slantEndAbove_nbr (hslantrun (k - 1) (by omega) (by omega))
        (show T.SlantEndAbove u (nbr (T.upCell u x (k - 1)) u) from by
          rw [hstep]; exact hslantrun k (by omega) hkm)
      rw [hstep] at hst
      exact SameStack.trans T hprev (T.sameStack_of_isStackedPair ⟨u, hst⟩)
  have hGchain : ∀ d k, k = s + 1 + d → k ≤ m →
      T.SameStack (walk (T.upCell u x (s + 1)) (u + 5) (n : ℤ))
        (walk (T.upCell u x k) (u + 5) (n : ℤ)) := by
    intro d
    induction d with
    | zero =>
      intro k hk _
      rw [show k = s + 1 from by omega]
      exact T.sameStack_refl _
    | succ d ih =>
      intro k hk hkm
      have hprev := ih (k - 1) (by omega) (by omega)
      have hstep : nbr (T.upCell u x (k - 1)) u = T.upCell u x k := by
        rw [← T.upCell_succ, show k - 1 + 1 = k from by omega]
      have hgstep : walk (T.upCell u x k) (u + 5) (n : ℤ)
          = nbr (walk (T.upCell u x (k - 1)) (u + 5) (n : ℤ)) u := by
        rw [← hstep, walk_nbr_comm]
      obtain ⟨hd0, hL0⟩ := hGdata (k - 1) (by omega) (by omega)
      obtain ⟨hd1, -⟩ := hGdata k (by omega) hkm
      rw [hgstep] at hd1 ⊢
      exact SameStack.trans T hprev (T.sameStack_nbr_of_dir_eq hv (by omega) hL0 hd0 hd1)
  obtain ⟨hdGm, hLGm⟩ := hGdata m (by omega) le_rfl
  obtain ⟨hdGs, hLGs⟩ := hGdata (s + 1) (by omega) (by omega)
  have hchainV : T.SameStack (T.upCell u x (s + 1)) (T.upCell u x m) :=
    hvchain (m - s - 1) m (by omega) le_rfl
  have hchainG : T.SameStack (walk (T.upCell u x (s + 1)) (u + 5) (n : ℤ))
      (walk (T.upCell u x m) (u + 5) (n : ℤ)) := hGchain (m - s - 1) m (by omega) le_rfl
  -- ### the new stack lies above the stack filling the space `A`
  have hcellm : nbr (walk (T.upCell u x m) (u + 5) ((n : ℤ) - 1)) (u + 5)
      = walk (T.upCell u x m) (u + 5) (n : ℤ) := by
    rw [← walk_succ]
    congr 1
    ring
  have hAboveA : T.StackAbove u (nbr (T.tail x) (u + 5)) (walk (T.upCell u x m) (u + 5) (n : ℤ)) := by
    have hAup : T.upCell u x (n - 1) = nbr (T.tail x) (u + 5) := T.upCell_tail hdx
    obtain ⟨iA, hiA⟩ : ∃ k : ℕ, T.idx (nbr (T.tail x) (u + 5)) = k := ⟨_, rfl⟩
    have hheadA : T.head (nbr (T.tail x) (u + 5)) = T.upCell u x (n - iA) := by
      rw [head, hdA, hiA, ← hAup]
      refine T.upCell_walk u x (n - 1) (-((iA : ℤ) - 1)) (n - iA) ?_
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : iA ≤ n)]
      push_cast
      ring
    have hmA : T.upCell u x m = nbr (T.head (nbr (T.tail x) (u + 5))) (u + 3) := by
      rw [hheadA, show n - iA = m + 1 from by omega]
      exact (T.upCell_pred u x m).symm
    have hkeyA := T.above_head_flank hv hn hdA hLA
    rw [← hmA, T.head_eq_walk_of_dir_add_two hdm him, hcellm] at hkeyA
    exact hkeyA.2.2
  -- ### the new stack lies above the second horizontal stack above
  have htailB : T.tail (T.upCell u x s) = T.upCell u x s := T.tail_upCell h0n hds his
  have hvB : T.upCell u x (s + 1) = nbr (T.tail (T.upCell u x s)) u := by
    rw [htailB]
    exact T.upCell_succ u x s
  have htopv : T.tail (T.upCell u x (s + 1))
      = walk (T.upCell u x (s + 1)) (u + 5) ((n : ℤ) - 1) :=
    T.tail_eq_walk_of_dir_add_five h0n hd5 hi5
  obtain ⟨z, hz, hzeq⟩ := T.exists_sameStack_of_mem_flankingStick hv (by omega) hLU
    (show T.tail (T.upCell u x (s + 1))
        ∈ T.stickOf (nbr (T.tail (T.upCell u x s)) (T.dir (T.upCell u x s))) from by
      rw [hds, ← hvB]
      exact T.tail_mem_stickOf h0n _)
  rw [hds] at hzeq
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLU hz, hds]
  have hLz : T.IsLeftLeaningStack z := T.isLeftLeaningStack_of_sameStack hLU hz
  obtain ⟨hdAz, hcaseAz⟩ := T.dir_backCorner_beyond_tail hv (by omega) hLU hds hz
  have hGeq : walk (T.upCell u x (s + 1)) (u + 5) (n : ℤ) = nbr (nbr (T.tail z) (u + 5)) u := by
    rw [show walk (T.upCell u x (s + 1)) (u + 5) (n : ℤ)
        = nbr (T.tail (T.upCell u x (s + 1))) (u + 5) from by
      rw [htopv, ← walk_succ]
      congr 1
      ring, ← hzeq, nbr_comm]
  have hAzlt : T.idx (nbr (T.tail z) (u + 5)) < n := by
    rcases hcaseAz with ⟨hifull, hsame⟩ | h
    · exfalso
      have hLAz : T.IsLeftLeaningStack (nbr (T.tail z) (u + 5)) :=
        T.isLeftLeaningStack_of_sameStack hLU hsame
      have htailAz : T.tail (nbr (T.tail z) (u + 5)) = nbr (T.tail z) (u + 5) :=
        (T.eq_tail_of_mem_of_idx_eq h0n (T.self_mem_stickOf _) hifull).symm
      have hf := T.dir_flank hv (by omega) hLAz hdAz
      rw [htailAz, ← hGeq] at hf
      exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdGs.symm.trans hf)
    · exact h.2
  have hmemG : walk (T.upCell u x (s + 1)) (u + 5) (n : ℤ)
      ∈ T.stickOf (nbr (T.tail z) (u + 5)) := by
    rw [hGeq]
    have hmem := T.nbr_dir_mem_stickOf (nbr (T.tail z) (u + 5)) hAzlt
    rwa [hdAz] at hmem
  obtain ⟨iz, hiz⟩ : ∃ k : ℕ, T.idx (nbr (T.tail z) (u + 5)) = k := ⟨_, rfl⟩
  have hfront : T.frontCell u (nbr (T.tail z) (u + 5))
      = T.frontCell u z + ((n : ℤ) - iz) • u.vec + (1 : ℤ) • (u + 5).vec := by
    rw [T.frontCell_eq_add h0n hdAz, T.frontCell_eq_add h0n hdz, hiz,
      show nbr (T.tail z) (u + 5) = z + ((n : ℤ) - T.idx z) • u.vec + (u + 5).vec from by
        rw [T.tail_eq_walk h0n z, hdz]
        simp only [walk, nbr]]
    module
  have hnotsame : ¬ T.SameStack z (nbr (T.tail z) (u + 5)) :=
    T.not_sameStack_of_frontCell_add hv (by omega) hLz hdz hfront (Or.inl (by omega))
  have hsameG : T.SameStack (walk (T.upCell u x m) (u + 5) (n : ℤ)) (nbr (T.tail z) (u + 5)) :=
    SameStack.trans T (SameStack.symm T hchainG) (T.sameStack_of_mem_stickOf hmemG)
  have hAboveB : T.StackAbove u (T.upCell u x s) (walk (T.upCell u x m) (u + 5) (n : ℤ)) := by
    refine ⟨?_, T.tail z, ?_, Or.inr hsameG⟩
    · intro hs
      exact hnotsame (SameStack.trans T (SameStack.symm T hz) (SameStack.trans T hs hsameG))
    · exact SameStack.trans T hz (T.sameStack_of_stickOf_eq
        (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n z)).symm)
  -- ### the vertical stack is adjacent to the four horizontal stacks
  have hnev : ∀ q : Hex, T.dir q = u → T.IsLeftLeaningStack q →
      ¬ T.SameStack (T.upCell u x (s + 1)) q := by
    intro q hdq hLq
    exact T.not_sameStack_of_dir_ne hv (by omega) hLq hdq
      (by rw [hd5]; exact (by decide : ∀ a : HexDir, a + 5 ≠ a) u)
  have hAdjc : T.StackAdjacent (T.upCell u x (s + 1)) c := by
    refine ⟨hnev c hu hL, T.upCell u x (s + 1), u + 2, T.sameStack_refl _, ?_⟩
    rw [show nbr (T.upCell u x (s + 1)) (u + 2) = walk (T.head x) u ((s + 1 : ℕ) : ℤ) from by
      rw [upCell]; exact nbr_nbr_cancel _ (opp_add_five u).symm]
    have hmemx : walk (T.head x) u ((s + 1 : ℕ) : ℤ) ∈ T.stickOf x := by
      rw [T.mem_stickOf_iff]
      exact ⟨s + 1, by omega, by rw [cellOfStick, hdx]⟩
    exact SameStack.trans T hx (SameStack.symm T (T.sameStack_of_mem_stickOf hmemx))
  have hAdjB : T.StackAdjacent (T.upCell u x (s + 1)) (T.upCell u x s) := by
    refine ⟨hnev _ hds hLU, T.upCell u x (s + 1), u + 3, T.sameStack_refl _, ?_⟩
    rw [T.upCell_pred u x s]
    exact T.sameStack_refl _
  have hAdjA : T.StackAdjacent (T.upCell u x (s + 1)) (nbr (T.tail x) (u + 5)) := by
    refine ⟨hnev _ hdA hLA, T.upCell u x m, u, hchainV, ?_⟩
    rw [show nbr (T.upCell u x m) u = T.upCell u x (m + 1) from (T.upCell_succ u x m).symm]
    exact SameStack.symm T (T.sameStack_of_mem_stickOf
      (T.upCell_mem_stickOf_backCorner h0n hdA hdx (by omega) (by omega)))
  have hAdja₃ : T.StackAdjacent (T.upCell u x (s + 1))
      (walk (T.upCell u x m) (u + 5) (n : ℤ)) := by
    refine ⟨hnev _ hdGm hLGm, walk (T.upCell u x m) (u + 5) ((n : ℤ) - 1), u + 5, ?_, ?_⟩
    · exact SameStack.trans T hchainV (SameStack.symm T (T.sameStack_of_mem_stickOf
        (T.slantEndBelow_topCell h0n (hslantrun m (by omega) le_rfl)).2))
    · rw [hcellm]
      exact T.sameStack_refl _
  -- ### the vertical stack contains at least two sticks
  have hheight : 2 ≤ T.stackHeight (T.upCell u x (s + 1)) := by
    have hstep : T.upCell u x (s + 2) = nbr (T.upCell u x (s + 1)) u := T.upCell_succ u x (s + 1)
    have hsl1 : T.SlantEndAbove u (T.upCell u x (s + 1)) := hslantrun (s + 1) (by omega) (by omega)
    have hsl2 : T.SlantEndAbove u (nbr (T.upCell u x (s + 1)) u) := by
      rw [← hstep]
      exact hslantrun (s + 2) (by omega) (by omega)
    have hst := T.stackedBy_of_slantEndAbove_nbr hsl1 hsl2
    have hsame : T.SameStack (T.upCell u x (s + 1)) (T.upCell u x (s + 2)) := by
      rw [hstep]
      exact T.sameStack_of_isStackedPair ⟨u, hst⟩
    have hnestick : T.stickOf (T.upCell u x (s + 1)) ≠ T.stickOf (T.upCell u x (s + 2)) := by
      intro heq
      have hmem : T.upCell u x (s + 2) ∈ T.stickOf (T.upCell u x (s + 1)) := by
        rw [heq]
        exact T.self_mem_stickOf _
      rw [T.stickOf_eq_image_of_slantEndAbove hsl1, Finset.mem_image] at hmem
      obtain ⟨k, -, hkeq⟩ := hmem
      rw [hstep] at hkeq
      have hkey : (1 : ℤ) • u.vec = (k : ℤ) • (u + 5).vec := by
        simp only [walk, nbr] at hkeq
        linear_combination (norm := module) -hkeq
      obtain ⟨h1, -⟩ := smul_vec_eq_smul_vec ((by decide : ∀ a : HexDir, a ≠ a + 5) u)
        (by rw [opp_add_five]; exact (by decide : ∀ a : HexDir, a ≠ a + 2) u) hkey
      exact one_ne_zero h1
    have hsub : ({T.stickOf (T.upCell u x (s + 1)), T.stickOf (T.upCell u x (s + 2))} :
        Set (Finset Hex)) ⊆ T.Stack (T.upCell u x (s + 1)) := by
      rintro S (rfl | rfl)
      · exact T.self_mem_stack _
      · exact ⟨T.upCell u x (s + 2), hsame, rfl⟩
    have hcard := Set.ncard_le_ncard hsub (T.stack_finite hv h0n _)
    rw [Set.ncard_pair hnestick] at hcard
    exact hcard
  exact ⟨walk (T.upCell u x m) (u + 5) (n : ℤ), T.upCell u x (s + 1), nbr (T.tail x) (u + 5),
    T.upCell u x s,
    fun a hda hab => T.stackAbove_classification hv hn hcov hL hu hx htop hds his hs2 hrow hda hab,
    hdGm, hAboveA, hAboveB, Or.inr hd5, hheight, hAdjc, hAdjA, hAdjB, hAdja₃⟩

/-- **The four horizontal stacks of a grid cell enclose a vertical stack.** -/
theorem grid_cell_of_weaveCell (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir}
    (hcov : ∀ z, T.WeaveCell u z) {c a₁ a₂ : Hex} (hu : T.dir c = u) (hu₁ : T.dir a₁ = u)
    (hu₂ : T.dir a₂ = u) (h₁ : T.StackAbove u c a₁) (h₂ : T.StackAbove u c a₂)
    (hne : ¬ T.SameStack a₁ a₂) :
    ∃ a₃ v, T.dir a₃ = u ∧ T.StackAbove u a₁ a₃ ∧ T.StackAbove u a₂ a₃ ∧
      T.SlantsLeft u v ∧ 2 ≤ T.stackHeight v ∧ T.StackAdjacent v c ∧ T.StackAdjacent v a₁ ∧
      T.StackAdjacent v a₂ ∧ T.StackAdjacent v a₃ := by
  obtain ⟨a₃, v, A, B, huniq, hda₃, hAboveA, hAboveB, hslv, hheight, hadjc, hadjA, hadjB,
    hadj3⟩ := T.grid_cell_core hv hn hcov hu
  have mk : ∀ b₁ b₂ : Hex, T.SameStack b₁ A → T.SameStack b₂ B →
      T.StackAbove u b₁ a₃ ∧ T.StackAbove u b₂ a₃ ∧
        T.StackAdjacent v b₁ ∧ T.StackAdjacent v b₂ := by
    intro b₁ b₂ hb₁ hb₂
    exact ⟨T.stackAbove_of_sameStack (SameStack.symm T hb₁) hAboveA,
      T.stackAbove_of_sameStack (SameStack.symm T hb₂) hAboveB,
      T.stackAdjacent_of_sameStack (SameStack.symm T hb₁) hadjA,
      T.stackAdjacent_of_sameStack (SameStack.symm T hb₂) hadjB⟩
  rcases huniq a₁ hu₁ h₁ with hc₁ | hc₁ <;> rcases huniq a₂ hu₂ h₂ with hc₂ | hc₂
  · exact absurd (SameStack.trans T hc₁ (SameStack.symm T hc₂)) hne
  · obtain ⟨k1, k2, k3, k4⟩ := mk a₁ a₂ hc₁ hc₂
    exact ⟨a₃, v, hda₃, k1, k2, hslv, hheight, hadjc, k3, k4, hadj3⟩
  · obtain ⟨k1, k2, k3, k4⟩ := mk a₂ a₁ hc₂ hc₁
    exact ⟨a₃, v, hda₃, k2, k1, hslv, hheight, hadjc, k4, k3, hadj3⟩
  · exact absurd (SameStack.trans T hc₁ (SameStack.symm T hc₂)) hne

end StickTiling

end StickPolyhex
