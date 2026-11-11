import Tiling.Proofs.StepStack

/-!
# The neighbours of a stick of a vertical stack are anchored

This file proves the second propagation step of the covering argument: every cell adjacent to a
cell of a left-slanting stick resting on a left-leaning stack is anchored.

The cells adjacent to such a stick `V` are treated in three groups.  Along the axis of `V`
(`StickTiling.anchored_axis_of_holeAbove`) one finds the other cells of `V` and the two cells
just beyond its ends, which are horizontal cells of left-leaning stacks by
`StickTiling.holeBelow_of_holeAbove` and by the anchoring stack itself.  On the two sides of `V`
(`StickTiling.side_of_holeAbove`) one finds either the neighbouring stick of the same vertical
stack, or the near ends, respectively the far ends, of the sticks of the horizontal stack that
`V` flanks.  The two remaining diagonal directions are a side step followed by a step along the
axis.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Along the stick -/

/-- **The two neighbours of a cell of a stick of a vertical stack along the axis of the stick
are anchored.**  They are cells of the stick itself, except at its two ends, where they are the
cells just beyond them. -/
theorem anchored_axis_of_holeAbove (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleAbove u z) :
    T.Anchored u (nbr z (u + 5)) ∧ T.Anchored u (nbr z (u + 2)) := by
  obtain ⟨p, hdp, hLp, hslant, hzmem⟩ := h
  set V := nbr p (u + 5) with hV
  have himg := T.stickOf_eq_image_of_slantEndAbove hslant
  have hmem : ∀ l : ℕ, l < n → walk V (u + 5) (l : ℤ) ∈ T.stickOf V := by
    intro l hl
    rw [himg, Finset.mem_image]
    exact ⟨l, Finset.mem_range.2 hl, rfl⟩
  have hanch : ∀ q ∈ T.stickOf V, T.Anchored u q := fun q hq =>
    Or.inr (Or.inl ⟨p, hdp, hLp, hslant, hq⟩)
  rw [himg, Finset.mem_image] at hzmem
  obtain ⟨k, hk, rfl⟩ := hzmem
  rw [Finset.mem_range] at hk
  constructor
  · rw [show nbr (walk V (u + 5) (k : ℤ)) (u + 5) = walk V (u + 5) ((k + 1 : ℕ) : ℤ) from
      (walk_nat_succ V (u + 5) k).symm]
    by_cases hkn : k + 1 < n
    · exact hanch _ (hmem _ hkn)
    · rw [show ((k + 1 : ℕ) : ℤ) = (n : ℤ) from by omega]
      obtain ⟨hdg, hLg⟩ := T.dir_isLeftLeaning_above_topCell hv hn hdp hLp hslant
      exact Or.inl ⟨hdg, hLg⟩
  · by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.cast_zero, walk_zero]
      rw [hV, nbr_nbr_cancel p (opp_add_five u).symm]
      exact Or.inl ⟨hdp, hLp⟩
    · rw [show nbr (walk V (u + 5) (k : ℤ)) (u + 2) = walk V (u + 5) ((k - 1 : ℕ) : ℤ) from by
        rw [show u + 2 = (u + 5).opp from (opp_add_five u).symm, nbr_eq_walk_one, walk_opp,
          walk_walk]
        congr 1
        omega]
      exact hanch _ (hmem _ (by omega))

/-! ### To the sides of the stick -/

/-- **The two neighbours of a cell of a stick of a vertical stack across the axis of the stick
lie on the neighbouring stick of the vertical stack, or on a horizontal stack.**  On each side
of the stick there is either a further stick of the vertical stack, or the horizontal stack it
flanks: on the right the stack filling the space `A`, whose near ends it flanks, and on the left
the second horizontal stack above, whose far ends it flanks. -/
theorem side_of_holeAbove (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleAbove u z) :
    ((T.dir (nbr z u) = u ∧ T.IsLeftLeaningStack (nbr z u)) ∨ T.HoleAbove u (nbr z u)) ∧
      ((T.dir (nbr z (u + 3)) = u ∧ T.IsLeftLeaningStack (nbr z (u + 3))) ∨
        T.HoleAbove u (nbr z (u + 3))) := by
  have h0n : 0 < n := by omega
  obtain ⟨p, hdp, hLp, hslant, hzmem⟩ := h
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
  obtain ⟨j, hj, hjeq⟩ : ∃ j, j < n ∧ nbr p (u + 5) = T.upCell u x j := by
    rcases T.up_classification hv (by omega) hLp hdp hx htop (T.sameStack_refl p) with hsame | hex
    · exfalso
      have hdv : T.dir (nbr p (u + 5)) = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLp hsame, hdp]
      rcases hslant with ⟨hd, -⟩ | ⟨hd, -⟩
      · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdv.symm.trans hd)
      · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdv.symm.trans hd)
    · exact hex
  rw [hjeq] at hslant hzmem
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv (by omega) hLp hdp hx hi1 hin
  obtain ⟨hdm, him⟩ := T.top_row_base hv (by omega) hLp hdp hx hi1 hin
  have hLs : T.IsLeftLeaningStack (T.upCell u x s) :=
    T.isLeftLeaningStack_upCell hv (by omega) hds his hd5 hi5
  set m := n - i - 1 with hmdef
  have hmn : m < n := by omega
  have hnotslant : ∀ k, k ≤ s → ¬ T.SlantEndAbove u (T.upCell u x k) := by
    intro k hk hsl
    have hmemk := T.upCell_mem_stickOf_of_le hds his (by omega) hk
    have hdk : T.dir (T.upCell u x k) = u := by rw [T.dir_of_mem_stickOf hmemk, hds]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  have hnotslant' : ∀ k, k < n → m < k → ¬ T.SlantEndAbove u (T.upCell u x k) := by
    intro k hkn hk hsl
    have hmemk : T.upCell u x k ∈ T.stickOf A :=
      T.upCell_mem_stickOf_backCorner h0n hdA hdx
        (show n - T.idx (nbr (T.tail x) (u + 5)) ≤ k by rw [← hAdef, ← hidef]; omega) hkn
    have hdk : T.dir (T.upCell u x k) = u := by rw [T.dir_of_mem_stickOf hmemk, hdA]
    rcases hsl with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact (by decide : ∀ a : HexDir, a ≠ a + 2) u (hdk.symm.trans hd)
    · exact (by decide : ∀ a : HexDir, a ≠ a + 5) u (hdk.symm.trans hd)
  have hslantrun : ∀ k, s < k → k ≤ m → T.SlantEndAbove u (T.upCell u x k) := by
    intro k hk hkm
    rcases hrow k hk (by omega) with hsl | hmemk
    · exact hsl
    · have hge := T.le_of_mem_stickOf_backCorner h0n hdA hdx (T.idx_le A) hmemk
      rw [← hAdef, ← hidef] at hge
      omega
  have hjs : s < j := by
    by_contra hcon
    exact hnotslant j (by omega) hslant
  have hjm : j ≤ m := by
    by_contra hcon
    exact hnotslant' j hj (by omega) hslant
  -- the stack of `p` below the row, used as the anchor of the neighbouring hole sticks
  have hanchor : ∀ k, k < n → T.dir (walk (T.head x) u (k : ℤ)) = u ∧
      T.IsLeftLeaningStack (walk (T.head x) u (k : ℤ)) := by
    intro k hk
    refine ⟨(T.dir_idx_rowBase hdx hk).1, ?_⟩
    have hmemx : walk (T.head x) u (k : ℤ) ∈ T.stickOf x := by
      rw [T.mem_stickOf_iff]
      exact ⟨k, hk, by rw [cellOfStick, hdx]⟩
    exact T.isLeftLeaningStack_of_sameStack hLp
      (SameStack.trans T hx (SameStack.symm T (T.sameStack_of_mem_stickOf hmemx)))
  constructor
  · -- the neighbour on the right
    by_cases hjlt : j < m
    · right
      have hsl1 : T.SlantEndAbove u (T.upCell u x j) := hslantrun j hjs hjm
      have hsl2 : T.SlantEndAbove u (nbr (T.upCell u x j) u) := by
        rw [← T.upCell_succ]
        exact hslantrun (j + 1) (by omega) (by omega)
      have hst := T.stackedBy_of_slantEndAbove_nbr hsl1 hsl2
      have hmemz : nbr z u ∈ T.stickOf (nbr (T.upCell u x j) u) := hst.2.2 z hzmem
      obtain ⟨hdq, hLq⟩ := hanchor (j + 1) (by omega)
      refine ⟨walk (T.head x) u ((j + 1 : ℕ) : ℤ), hdq, hLq, ?_, ?_⟩
      · rw [show nbr (walk (T.head x) u ((j + 1 : ℕ) : ℤ)) (u + 5) = T.upCell u x (j + 1) from rfl,
          T.upCell_succ]
        exact hsl2
      · rw [show nbr (walk (T.head x) u ((j + 1 : ℕ) : ℤ)) (u + 5) = T.upCell u x (j + 1) from rfl,
          T.upCell_succ]
        exact hmemz
    · left
      have hjm' : j = m := by omega
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
      rw [hjm', hmA] at hzmem
      have hne3 : u ≠ u + 3 := (by decide : ∀ a : HexDir, a ≠ a + 3) u
      have hfc : T.frontCell (u + 3) A = nbr (T.head A) (u + 3) := by
        rw [frontCell, endCell, if_neg (by rw [hdA]; exact hne3)]
      obtain ⟨x', hx', hx'eq⟩ := T.exists_sameStack_frontCell_eq hv (by omega) hLA
        (show SameAxis (u + 3) (T.dir A) from Or.inr (by rw [hdA, opp_add_three]))
        (by rw [hfc]; exact hzmem)
      have hdx' : T.dir x' = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLA hx', hdA]
      rw [show T.frontCell (u + 3) x' = nbr (T.head x') (u + 3) from by
        rw [frontCell, endCell, if_neg (by rw [hdx']; exact hne3)]] at hx'eq
      have hzu : nbr z u = T.head x' := by
        rw [← hx'eq]
        exact nbr_nbr_cancel _ (opp_add_three u).symm
      rw [hzu]
      refine ⟨by rw [T.dir_head, hdx'], ?_⟩
      exact T.isLeftLeaningStack_of_sameStack hLA
        (SameStack.trans T hx'
          (SameStack.symm T (T.sameStack_of_mem_stickOf (T.head_mem_stickOf x'))))
  · -- the neighbour on the left
    by_cases hjgt : s + 1 < j
    · right
      have hsl0 : T.SlantEndAbove u (T.upCell u x (j - 1)) := hslantrun (j - 1) (by omega) (by omega)
      have hjstep : nbr (T.upCell u x (j - 1)) u = T.upCell u x j := by
        rw [← T.upCell_succ, show j - 1 + 1 = j from by omega]
      have hsl1 : T.SlantEndAbove u (nbr (T.upCell u x (j - 1)) u) := by
        rw [hjstep]
        exact hslantrun j hjs hjm
      have hst := StackedBy.symm T (T.stackedBy_of_slantEndAbove_nbr hsl0 hsl1)
      rw [hjstep] at hst
      have hmemz : nbr z (u + 3) ∈ T.stickOf (T.upCell u x (j - 1)) := by
        have hmz := hst.2.2 z hzmem
        rwa [opp_eq_add_three] at hmz
      obtain ⟨hdq, hLq⟩ := hanchor (j - 1) (by omega)
      refine ⟨walk (T.head x) u ((j - 1 : ℕ) : ℤ), hdq, hLq, ?_, ?_⟩
      · rw [show nbr (walk (T.head x) u ((j - 1 : ℕ) : ℤ)) (u + 5) = T.upCell u x (j - 1) from rfl]
        exact hsl0
      · rw [show nbr (walk (T.head x) u ((j - 1 : ℕ) : ℤ)) (u + 5) = T.upCell u x (j - 1) from rfl]
        exact hmemz
    · left
      have hjs' : j = s + 1 := by omega
      have hB : T.upCell u x (s + 1) = nbr (T.tail (T.upCell u x s)) u := by
        rw [T.tail_upCell h0n hds his]
        exact T.upCell_succ u x s
      rw [hjs', hB] at hzmem
      obtain ⟨x', hx', hx'eq⟩ := T.exists_sameStack_of_mem_flankingStick hv (by omega) hLs
        (by rw [hds]; exact hzmem)
      rw [hds] at hx'eq
      have hdx' : T.dir x' = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hLs hx', hds]
      have hzu : nbr z (u + 3) = T.tail x' := by
        rw [← hx'eq]
        exact nbr_nbr_cancel _ (opp_eq_add_three u).symm
      rw [hzu]
      refine ⟨by rw [T.dir_tail h0n, hdx'], ?_⟩
      exact T.isLeftLeaningStack_of_sameStack hLs
        (SameStack.trans T hx'
          (SameStack.symm T (T.sameStack_of_mem_stickOf (T.tail_mem_stickOf h0n x'))))

/-! ### All the neighbours -/

/-- **The neighbours of a stick of a vertical stack are anchored.** -/
theorem anchored_nbr_of_holeAbove (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleAbove u z) (e : HexDir) : T.Anchored u (nbr z e) := by
  obtain ⟨hup, hdown⟩ := T.anchored_axis_of_holeAbove hv hn h
  obtain ⟨heast, hwest⟩ := T.side_of_holeAbove hv hn h
  have he : e = u ∨ e = u + 1 ∨ e = u + 2 ∨ e = u + 3 ∨ e = u + 4 ∨ e = u + 5 :=
    (by decide : ∀ a b : HexDir,
      b = a ∨ b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b = a + 4 ∨ b = a + 5) u e
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases heast with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  · rw [show nbr z (u + 1) = nbr (nbr z u) (u + 2) from
      (nbr_nbr_of_vec z ((by decide +kernel : ∀ a : HexDir,
        a.vec + (a + 2).vec = (a + 1).vec) u)).symm]
    rcases heast with ⟨hd, hL⟩ | hh
    · exact T.anchored_nbr_of_leftLeaning hv hn hL hd (T.sameStack_refl _) (u + 2)
    · exact (T.anchored_axis_of_holeAbove hv hn hh).2
  · exact hdown
  · rcases hwest with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  · rw [show nbr z (u + 4) = nbr (nbr z (u + 3)) (u + 5) from
      (nbr_nbr_of_vec z ((by decide +kernel : ∀ a : HexDir,
        (a + 3).vec + (a + 5).vec = (a + 4).vec) u)).symm]
    rcases hwest with ⟨hd, hL⟩ | hh
    · exact T.anchored_nbr_of_leftLeaning hv hn hL hd (T.sameStack_refl _) (u + 5)
    · exact (T.anchored_axis_of_holeAbove hv hn hh).1
  · exact hup

/-- The mirror statement, for a left-slanting stick resting against a left-leaning stack from
below; it reduces to `anchored_nbr_of_holeAbove` because such a stick also rests on a
left-leaning stack from above. -/
theorem anchored_nbr_of_holeBelow (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.HoleBelow u z) (e : HexDir) : T.Anchored u (nbr z e) :=
  T.anchored_nbr_of_holeAbove hv hn (T.holeAbove_of_holeBelow hv hn h) e

/-- **A neighbour of an anchored cell is anchored.** -/
theorem anchored_nbr (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {z : Hex}
    (h : T.Anchored u z) (e : HexDir) : T.Anchored u (nbr z e) := by
  rcases h with ⟨hd, hL⟩ | h | h
  · exact T.anchored_nbr_of_leftLeaning hv hn hL hd (T.sameStack_refl z) e
  · exact T.anchored_nbr_of_holeAbove hv hn h e
  · exact T.anchored_nbr_of_holeBelow hv hn h e

/-- **Every cell of a valid tiling is a weave cell.**  In a valid tiling by sticks of length
`n ≥ 5` there is an orientation `u` -- the direction of the sticks of any left-leaning stack --
for which every cell of the plane is covered as in the weave pattern. -/
theorem exists_weaveCell_all (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) :
    ∃ u : HexDir, (∃ c, T.dir c = u ∧ T.IsLeftLeaningStack c) ∧ ∀ z, T.WeaveCell u z := by
  obtain ⟨c, hL⟩ := T.exists_isLeftLeaningStack hv (by omega)
  refine ⟨T.dir c, ⟨c, rfl, hL⟩, fun z => T.weaveCell_of_anchored hv hn ?_⟩
  exact forall_of_nbr_closed (P := fun w => T.Anchored (T.dir c) w) (z₀ := c) (Or.inl ⟨rfl, hL⟩)
    (fun w hw e => T.anchored_nbr hv hn hw e) z

end StickTiling

end StickPolyhex
