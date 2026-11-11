import Tiling.Proofs.StackNeighbours

/-!
# A left-leaning stack meets exactly four left-leaning stacks

This file completes the analysis of the neighbourhood of a left-leaning stack in a valid tiling
by sticks of length `n ≥ 3`.  `Tiling/Proofs/StackTop.lean` and
`Tiling/Proofs/StackBottom.lean` produced two left-leaning stacks above and two below;
`Tiling/Proofs/StackNeighbours.lean` listed all the cells adjacent to the stack and showed that
the sticks flanking the stack, and the ends of the left-slanting sticks bordering it, do not lie
in left-leaning stacks.

Putting these together, `StickTiling.exists_four_leftLeaningStack_neighbours` shows that a
left-leaning stack has exactly four left-leaning neighbouring stacks: its top-left, top-right,
bottom-left and bottom-right neighbours, which are pairwise distinct, and every left-leaning
stack adjacent to it is one of these four.  This is the local structure of the weave pattern of
Lemma 4 of the paper.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- Two cells of one stick lie in the same stack. -/
lemma sameStack_of_mem_stickOf {a b : Hex} (h : a ∈ T.stickOf b) : T.SameStack a b :=
  T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem h)

/-- The cell just beyond the far end of a horizontal stick, in coordinates. -/
lemma frontCell_eq_add (hn : 0 < n) {z : Hex} {u : HexDir} (hdz : T.dir z = u) :
    T.frontCell u z = z + ((n : ℤ) - T.idx z + 1) • u.vec := by
  rw [T.frontCell_eq_walk hn hdz, walk]

/-- The cells of the row below a stack that precede the far end of the horizontal stick filling
the space beyond the near end of the stack all belong to that stick. -/
lemma downCell_mem_stickOf_of_le {y : Hex} {u : HexDir} {j : ℕ}
    (hdC : T.dir (T.downCell u y 0) = u) (hj : j ≤ n - T.idx (T.downCell u y 0)) :
    T.downCell u y j ∈ T.stickOf (T.downCell u y 0) := by
  have hpos := T.idx_pos (T.downCell u y 0)
  have hle := T.idx_le (T.downCell u y 0)
  rw [T.mem_stickOf_iff]
  refine ⟨T.idx (T.downCell u y 0) - 1 + j, by omega, ?_⟩
  rw [cellOfStick, head, hdC, walk_walk]
  exact T.downCell_walk u y 0 _ j (by push_cast; omega)

/-- **Every left-leaning stack meets exactly four left-leaning stacks.**  Let `c` be a
left-leaning stack of horizontal sticks of direction `u` in a valid tiling by sticks of length
`n ≥ 3`.  Then there are four pairwise distinct left-leaning stacks of horizontal sticks of the
same direction, two above `c` and two below it -- its top-left, top-right, bottom-left and
bottom-right neighbours -- and *every* left-leaning stack adjacent to `c` is one of them.

The stack `a₁` fills the space diagonally beyond the far ends of the sticks of `c` and `a₂` the
space diagonally beyond their near ends, so that `a₁` and `a₂` lie on opposite sides above `c`;
likewise `b₁` lies below `c` beyond the near ends of its sticks and `b₂` beyond their far
ends. -/
theorem exists_four_leftLeaningStack_neighbours (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c : Hex}
    {u : HexDir} (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ a₁ a₂ b₁ b₂ : Hex,
      (T.dir a₁ = u ∧ T.IsLeftLeaningStack a₁ ∧ T.StackAbove u c a₁) ∧
      (T.dir a₂ = u ∧ T.IsLeftLeaningStack a₂ ∧ T.StackAbove u c a₂) ∧
      (T.dir b₁ = u ∧ T.IsLeftLeaningStack b₁ ∧ T.StackBelow u c b₁) ∧
      (T.dir b₂ = u ∧ T.IsLeftLeaningStack b₂ ∧ T.StackBelow u c b₂) ∧
      ¬ T.SameStack a₁ a₂ ∧ ¬ T.SameStack b₁ b₂ ∧
      ¬ T.SameStack a₁ b₁ ∧ ¬ T.SameStack a₁ b₂ ∧
      ¬ T.SameStack a₂ b₁ ∧ ¬ T.SameStack a₂ b₂ ∧
      ∀ z, T.IsLeftLeaningStack z → T.StackAdjacent c z →
        T.SameStack z a₁ ∨ T.SameStack z a₂ ∨ T.SameStack z b₁ ∨ T.SameStack z b₂ := by
  have h0n : 0 < n := by omega
  have hdF : T.dir (nbr (T.tail c) u) = u + 5 := T.dir_flank hv (by omega) hL hu
  -- ### the topmost stick `x` and the row above it
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
    rcases T.isLeftLeaningStack_backCorner hv hn hL hu hx with h | h
    · exact absurd h hneA
    · exact h
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv hn hL hu hx hi1 hin
  have hLU : T.IsLeftLeaningStack (T.upCell u x s) :=
    T.isLeftLeaningStack_upCell hv (by omega) hds his hd5 hi5
  -- ### the bottommost stick `y` and the row below it
  obtain ⟨y, hy, hneC⟩ := T.exists_frontCorner_not_sameStack hv (by omega) hL hu
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hy, hu]
  have hbot := T.tail_nbr_eq_head_flank hv (by omega) hL hu hy hneC
  obtain ⟨hdC, hcaseC⟩ := T.dir_frontCorner_beyond_head hv (by omega) hL hu hy
  rw [← T.downCell_zero u y] at hdC hneC hcaseC
  obtain ⟨hiC1, hiCn⟩ :
      1 < T.idx (T.downCell u y 0) ∧ T.idx (T.downCell u y 0) < n := by
    rcases hcaseC with ⟨-, hsame⟩ | h
    · exact absurd hsame hneC
    · exact h
  have hLC : T.IsLeftLeaningStack (T.downCell u y 0) := by
    rcases T.isLeftLeaningStack_frontCorner hv hn hL hu hy with h | h
    · rw [← T.downCell_zero u y] at h
      exact absurd h hneC
    · rw [← T.downCell_zero u y] at h
      exact h
  obtain ⟨hdt, hit⟩ := T.downCell_tail_of_frontCorner hdC
  obtain ⟨w, hw1, hwn, hdw, hiw, hd2', hi2', hslantB⟩ := T.bot_row_ascend hv (by omega) hdy
    (t := n - T.idx (T.downCell u y 0)) (by omega) (by omega) ⟨hdt, hit⟩
  have hLW : T.IsLeftLeaningStack (T.downCell u y w) :=
    T.isLeftLeaningStack_downCell hv (by omega) (by omega) hdw hiw hd2' hi2'
  -- ### the cells of the two rows lie against the horizontal sticks of the stack
  have hbelowRow : ∀ j, j < n → T.dir (nbr (T.upCell u x j) (u + 2)) = u := by
    intro j hj
    rw [show nbr (T.upCell u x j) (u + 2) = walk (T.head x) u (j : ℤ) from by
      rw [upCell]; exact nbr_nbr_cancel _ (opp_add_five u).symm]
    exact (T.dir_idx_rowBase hdx hj).1
  have haboveRow : ∀ j, j < n → T.dir (nbr (T.downCell u y j) (u + 5)) = u := by
    intro j hj
    rw [show nbr (T.downCell u y j) (u + 5) = walk (T.head y) u (j : ℤ) from by
      rw [downCell]; exact nbr_nbr_cancel _ (opp_add_two u).symm]
    exact (T.dir_idx_rowBase hdy hj).1
  -- ### the position of the bottommost stick relative to the topmost one
  have htx : T.tail x = walk (T.head x) u ((n : ℤ) - 1) := by
    rw [tail, cellOfStick, hdx, show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 from by omega]
  have hty : T.tail y = walk (T.head y) u ((n : ℤ) - 1) := by
    rw [tail, cellOfStick, hdy, show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 from by omega]
  have hFt : T.tail (nbr (T.tail c) u)
      = walk (T.head (nbr (T.tail c) u)) (u + 5) ((n : ℤ) - 1) := by
    rw [tail, cellOfStick, hdF, show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 from by omega]
  have hheady : T.head y = T.head x + (-((n : ℤ) - 1)) • (u + 5).vec := by
    rw [htx, hFt] at htop
    rw [hty] at hbot
    simp only [walk, nbr] at htop hbot ⊢
    linear_combination (norm := module) hbot - htop
  have hvec2 : (u + 2).vec = -(u + 5).vec := (by decide : ∀ a : HexDir, (a + 2).vec
    = -(a + 5).vec) u
  -- ### the four stacks, in coordinates
  have hAcoord : nbr (T.tail x) (u + 5)
      = T.head x + ((n : ℤ) - 1) • u.vec + (1 : ℤ) • (u + 5).vec := by
    rw [htx]
    simp only [walk, nbr]
    module
  have hUcoord : T.upCell u x s = T.head x + (s : ℤ) • u.vec + (1 : ℤ) • (u + 5).vec := by
    simp only [upCell, walk, nbr]
    module
  have hCcoord : T.downCell u y 0
      = T.head x + (0 : ℤ) • u.vec + (-(n : ℤ)) • (u + 5).vec := by
    rw [downCell, hheady]
    simp only [walk, nbr, hvec2]
    module
  have hWcoord : T.downCell u y w
      = T.head x + (w : ℤ) • u.vec + (-(n : ℤ)) • (u + 5).vec := by
    rw [downCell, hheady]
    simp only [walk, nbr, hvec2]
    module
  have habs : (n : ℤ) ≤ |(-(n : ℤ) - 1)| := by
    rw [abs_of_nonpos (by omega : (-(n : ℤ) - 1) ≤ 0)]
    omega
  -- ### the two stacks above and the two stacks below are distinct
  have hne12 : ¬ T.SameStack (nbr (T.tail x) (u + 5)) (T.upCell u x s) :=
    T.not_sameStack_backCorner_upCell hv (by omega) hLA hdA hdx hds his hs2
  have hne34 : ¬ T.SameStack (T.downCell u y 0) (T.downCell u y w) :=
    T.not_sameStack_frontCorner_downCell hv (by omega) hLC hdC rfl (by omega) (by omega) hdw hiw
  obtain ⟨iA, hiAdef⟩ : ∃ i : ℕ, T.idx (nbr (T.tail x) (u + 5)) = i := ⟨_, rfl⟩
  obtain ⟨iC, hiCdef⟩ : ∃ i : ℕ, T.idx (T.downCell u y 0) = i := ⟨_, rfl⟩
  have hne13 : ¬ T.SameStack (nbr (T.tail x) (u + 5)) (T.downCell u y 0) := by
    refine T.not_sameStack_of_frontCell_add hv (by omega) hLA hdA (b := -(n : ℤ) - 1)
      (a := (iA : ℤ) - (iC : ℤ) - (n : ℤ) + 1) ?_ (Or.inr habs)
    rw [T.frontCell_eq_add h0n hdC, T.frontCell_eq_add h0n hdA, hiAdef, hiCdef, hCcoord, hAcoord]
    module
  have hne14 : ¬ T.SameStack (nbr (T.tail x) (u + 5)) (T.downCell u y w) := by
    refine T.not_sameStack_of_frontCell_add hv (by omega) hLA hdA (b := -(n : ℤ) - 1)
      (a := (w : ℤ) + (iA : ℤ) - (n : ℤ)) ?_ (Or.inr habs)
    rw [T.frontCell_eq_add h0n hdw, T.frontCell_eq_add h0n hdA, hiAdef, hiw, hWcoord, hAcoord]
    module
  have hne23 : ¬ T.SameStack (T.upCell u x s) (T.downCell u y 0) := by
    refine T.not_sameStack_of_frontCell_add hv (by omega) hLU hds (b := -(n : ℤ) - 1)
      (a := (n : ℤ) - (iC : ℤ) - (s : ℤ)) ?_ (Or.inr habs)
    rw [T.frontCell_eq_add h0n hdC, T.frontCell_eq_add h0n hds, hiCdef, his, hCcoord, hUcoord]
    module
  have hne24 : ¬ T.SameStack (T.upCell u x s) (T.downCell u y w) := by
    refine T.not_sameStack_of_frontCell_add hv (by omega) hLU hds (b := -(n : ℤ) - 1)
      (a := (w : ℤ) + (n : ℤ) - (s : ℤ) - 1) ?_ (Or.inr habs)
    rw [T.frontCell_eq_add h0n hdw, T.frontCell_eq_add h0n hds, hiw, his, hWcoord, hUcoord]
    module
  -- ### the four stacks are neighbours of the stack through `c`
  have hAbove1 : T.StackAbove u c (nbr (T.tail x) (u + 5)) := by
    refine ⟨hneA, T.tail x, SameStack.trans T hx (T.sameStack_of_stickOf_eq
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
  -- ### every left-leaning stack adjacent to `c` is one of the four
  refine ⟨nbr (T.tail x) (u + 5), T.upCell u x s, T.downCell u y 0, T.downCell u y w,
    ⟨hdA, hLA, hAbove1⟩, ⟨hds, hLU, hAbove2⟩, ⟨hdC, hLC, hBelow1⟩, ⟨hdw, hLW, hBelow2⟩,
    hne12, hne34, hne13, hne14, hne23, hne24, ?_⟩
  intro z hLz hadj
  obtain ⟨hnez, p, e, hp, hze⟩ := hadj
  rcases T.nbr_classification hv (by omega) hL hu hx htop hy hbot hp e with
    hcs | hmF | hmE | ⟨j, hj, hjeq⟩ | hcorner | ⟨j, hj, hjeq⟩
  · exact absurd (SameStack.trans T hcs (SameStack.symm T hze)) hnez
  · exact absurd (T.isLeftLeaningStack_of_sameStack hLz
      (SameStack.trans T hze (T.sameStack_of_mem_stickOf hmF)))
      (T.not_isLeftLeaningStack_flank hv (by omega) hL hu hx htop hin)
  · exact absurd (T.isLeftLeaningStack_of_sameStack hLz
      (SameStack.trans T hze (T.sameStack_of_mem_stickOf hmE)))
      (T.not_isLeftLeaningStack_frontFlank hv (by omega) hL hu hx htop hds his hs2)
  · rw [hjeq] at hze
    rcases Nat.lt_or_ge s j with hjs | hjs
    · rcases hrow j hjs hj with hslant | hmem
      · exact absurd (T.isLeftLeaningStack_of_sameStack hLz hze)
          (T.not_isLeftLeaningStack_slantEndAbove hv (by omega) hslant (hbelowRow j hj))
      · exact Or.inl (SameStack.trans T hze (T.sameStack_of_mem_stickOf hmem))
    · exact Or.inr (Or.inl (SameStack.trans T hze (T.sameStack_of_mem_stickOf
        (T.upCell_mem_stickOf_of_le hds his (by omega) hjs))))
  · rw [hcorner] at hze
    exact Or.inr (Or.inl (SameStack.trans T hze (T.sameStack_of_mem_stickOf
      (T.backCorner_head_mem_stickOf hds his hs2))))
  · rw [hjeq] at hze
    rcases Nat.lt_or_ge (n - T.idx (T.downCell u y 0)) j with hjt | hjt
    · rcases Nat.lt_or_ge j w with hjw | hjw
      · exact absurd (T.isLeftLeaningStack_of_sameStack hLz hze)
          (T.not_isLeftLeaningStack_slantEndBelow hv (by omega) (hslantB j hjt hjw)
            (haboveRow j (by omega)))
      · exact Or.inr (Or.inr (Or.inr (SameStack.trans T hze (T.sameStack_of_mem_stickOf
          (T.downCell_mem_stickOf_of_ge hdw hiw hjw (by omega))))))
    · exact Or.inr (Or.inr (Or.inl (SameStack.trans T hze
        (T.sameStack_of_mem_stickOf (T.downCell_mem_stickOf_of_le hdC hjt)))))

end StickTiling

end StickPolyhex
