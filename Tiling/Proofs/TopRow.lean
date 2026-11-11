import Tiling.Proofs.WeaveUp

/-!
# The row of cells above a left-leaning stack

This file carries out the analysis of Figure 16 of the paper: the cells lying on the back side
of the topmost stick of a left-leaning stack are covered, from the far end towards the near end,
first by the horizontal stick `T` filling the space `A`, then by the left-slanting sticks of a
vertical stack, and finally by a second horizontal stick `U` filling the space `B`.

The three lemmas of this section are the local steps of that analysis.  Throughout, `p` is a
cell of the topmost stick of the stack, of direction `u`, and `z = nbr p (u + 5)` is the cell of
the row sitting above it; the cell of the row one step further towards the far end is
`nbr z u = nbr (nbr p u) (u + 5)`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- **A left-slanting stick with its arrow pointing away from the near end cannot sit above the
head of a horizontal stick.**  The cell above the head of a horizontal stick presents the label
`a₁`, which by rule 5 cannot meet a `y` label. -/
lemma top_no_slant_head (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hp1 : T.idx p = 1) :
    ¬ ((T.dir (nbr p (u + 5)) = u + 2 ∧ T.idx (nbr p (u + 5)) = n) ∨
      (T.dir (nbr p (u + 5)) = u + 5 ∧ T.idx (nbr p (u + 5)) = 1)) := by
  set z := nbr p (u + 5) with hz
  have hA : T.label p (u + 5) = some (.a 1) := by
    rw [T.label_shift5 (u := u) (k := 0) (by rw [hdp, add_zero])
      (by decide : (5 : HexDir) = 0 + 5), if_neg (by omega), hp1]
  have hAface : ∀ Q, T.label z (u + 2) = some Q → ¬ Forbidden n (.a 1) Q := fun Q hQ hf =>
    T.clash hv hA (by rw [opp_add_five]; exact hQ) hf
  rintro (⟨hd, hi⟩ | ⟨hd, hi⟩)
  · exact hAface .y2
      (by rw [T.label_shift0 (u := u) (k := 2) (j := 2) hd rfl, if_pos hi])
      (Or.inr (ForbiddenCore.rule5 (Or.inr rfl) (Or.inl rfl)))
  · exact hAface .y1
      (by rw [T.label_shift3 (u := u) (k := 5) (j := 2) hd (by decide : (2 : HexDir) = 5 + 3),
        if_pos hi])
      (Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inl rfl)))

/-- **Step of the row analysis, past a left-slanting stick with its arrow pointing towards the
near end.**  If the cell of the row beyond `z` (towards the far end of the stack) is the last
cell of a stick of direction `u + 2`, then `z` itself is again the end of a left-slanting stick,
and `p` is not the head of its stick. -/
lemma top_step_two (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hpn : T.idx p < n)
    (hd' : T.dir (nbr (nbr p u) (u + 5)) = u + 2)
    (hi' : T.idx (nbr (nbr p u) (u + 5)) = n) :
    2 ≤ T.idx p ∧
      ((T.dir (nbr p (u + 5)) = u + 2 ∧ T.idx (nbr p (u + 5)) = n) ∨
        (T.dir (nbr p (u + 5)) = u + 5 ∧ T.idx (nbr p (u + 5)) = 1)) := by
  have hpos := T.idx_pos p
  set z := nbr p (u + 5) with hz
  set z' := nbr (nbr p u) (u + 5) with hz'
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  have hzz' : nbr z u = z' := by rw [hz, hz']; exact nbr_comm p (u + 5) u
  have hdpu : T.dir (nbr p u) = u := by
    have := T.succ_dir p hpn; rwa [hdp] at this
  have hipu : T.idx (nbr p u) = T.idx p + 1 := by
    have := T.succ_idx p hpn; rwa [hdp] at this
  -- the three labels facing `z`
  have hA : T.label p (u + 5) = some (.a (T.idx p)) := by
    rw [T.label_shift5 (u := u) (k := 0) (by rw [hdp, add_zero])
      (by decide : (5 : HexDir) = 0 + 5), if_neg (by omega)]
  have hAface : ∀ Q, T.label z (u + 2) = some Q → ¬ Forbidden n (.a (T.idx p)) Q :=
    fun Q hQ hf => T.clash hv hA (by rw [opp_add_five]; exact hQ) hf
  have hAnone : T.label z (u + 2) ≠ none := fun h =>
    T.no_none hA (by rw [opp_add_five]; exact h)
  have hBnbr : nbr (nbr p u) (u + 4) = z := nbr_nbr_of_vec p (vec_zero_four u)
  have hB : T.label (nbr p u) (u + 4) = some (.b (T.idx p)) := by
    rw [T.label_shift4 (u := u) (k := 0) (by rw [hdpu, add_zero])
      (by decide : (4 : HexDir) = 0 + 4), if_neg (by omega), hipu]
    simp
  have hBface : ∀ Q, T.label z (u + 1) = some Q → ¬ Forbidden n (.b (T.idx p)) Q :=
    fun Q hQ hf => T.clash hv hB (by rw [hBnbr, opp_add_four]; exact hQ) hf
  have hBnone : T.label z (u + 1) ≠ none := fun h =>
    T.no_none hB (by rw [hBnbr, opp_add_four]; exact h)
  have hZnbr : nbr z' (u + 3) = z := by
    rw [← hzz']; exact nbr_nbr_cancel z (opp_eq_add_three u).symm
  have hZ : T.label z' (u + 3) = some .z2 := by
    rw [T.label_shift1 (u := u) (k := 2) (j := 3) hd' (by decide : (3 : HexDir) = 2 + 1),
      if_pos hi']
  have hZface : ∀ Q, T.label z (u + 0) = some Q → ¬ Forbidden n .z2 Q := fun Q hQ hf =>
    T.clash hv hZ (by rw [hZnbr, opp_add_three']; exact hQ) hf
  have hZnone : T.label z (u + 0) ≠ none := fun h =>
    T.no_none hZ (by rw [hZnbr, opp_add_three']; exact h)
  rcases hexDir_cases u (T.dir z) with hk | hk | hk | hk | hk | hk
  · -- `z` horizontal: impossible next to the end of a left-slanting stick
    exfalso
    have hd0 : T.dir z = u + 0 := by rw [hk, add_zero]
    by_cases hi : T.idx z = n
    · exact hZface .y2 (by rw [T.label_shift0 (u := u) (k := 0) (j := 0) hd0 rfl, if_pos hi])
        (Or.inr (ForbiddenCore.rule10 (Or.inr rfl)))
    · exact hZnone (by rw [T.label_shift0 (u := u) (k := 0) (j := 0) hd0 rfl, if_neg hi])
  · exfalso
    have hi : T.idx z ≠ n := by
      intro hi
      exact hZface .x2 (by rw [T.label_shift5 (u := u) (k := 1) (j := 0) hk
        (by decide : (0 : HexDir) = 1 + 5), if_pos hi])
        (Or.inr (ForbiddenCore.rule4 (Or.inr rfl) (Or.inr rfl)))
    exact hBnone (by rw [T.label_shift0 (u := u) (k := 1) (j := 1) hk rfl, if_neg hi])
  · -- `z` is the last cell of a stick of direction `u + 2`
    have hi : T.idx z = n := by
      by_contra hi
      exact hAnone (by rw [T.label_shift0 (u := u) (k := 2) (j := 2) hk rfl, if_neg hi])
    refine ⟨?_, Or.inl ⟨hk, hi⟩⟩
    by_contra hp1
    have hp1' : T.idx p = 1 := by omega
    exact hAface .y2 (by rw [T.label_shift0 (u := u) (k := 2) (j := 2) hk rfl, if_pos hi])
      (by rw [hp1']; exact Or.inr (ForbiddenCore.rule5 (Or.inr rfl) (Or.inl rfl)))
  · exfalso
    by_cases hi : T.idx z = 1
    · exact hZface .y1 (by rw [T.label_shift3 (u := u) (k := 3) (j := 0)
        (by rw [hk]) (by decide : (0 : HexDir) = 3 + 3), if_pos hi])
        (Or.inr (ForbiddenCore.rule10 (Or.inl rfl)))
    · exact hZnone (by rw [T.label_shift3 (u := u) (k := 3) (j := 0)
        (by rw [hk]) (by decide : (0 : HexDir) = 3 + 3), if_neg hi])
  · exfalso
    have hi : T.idx z ≠ 1 := by
      intro hi
      exact hZface .x1 (by rw [T.label_shift2 (u := u) (k := 4) (j := 0) hk
        (by decide : (0 : HexDir) = 4 + 2), if_pos hi])
        (Or.inr (ForbiddenCore.rule4 (Or.inl rfl) (Or.inr rfl)))
    exact hBnone (by rw [T.label_shift3 (u := u) (k := 4) (j := 1) hk
      (by decide : (1 : HexDir) = 4 + 3), if_neg hi])
  · -- `z` is the first cell of a stick of direction `u + 5`
    have hin : T.idx z ≠ n := by
      intro hi
      exact hZface .z2 (by rw [T.label_shift1 (u := u) (k := 5) (j := 0) hk
        (by decide : (0 : HexDir) = 5 + 1), if_pos hi])
        (Or.inl (ForbiddenCore.rule2z (Or.inr rfl) (Or.inr rfl)))
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hZface (.d (n - T.idx z)) (by rw [T.label_shift1 (u := u) (k := 5) (j := 0) hk
        (by decide : (0 : HexDir) = 5 + 1), if_neg hin])
        (Or.inl (ForbiddenCore.rule7 (by omega) (by omega)))
    refine ⟨?_, Or.inr ⟨hk, hi⟩⟩
    by_contra hp1
    have hp1' : T.idx p = 1 := by omega
    exact hAface .y1 (by rw [T.label_shift3 (u := u) (k := 5) (j := 2) hk
      (by decide : (2 : HexDir) = 5 + 3), if_pos hi])
      (by rw [hp1']; exact Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inl rfl)))

/-- **Step of the row analysis, past a left-slanting stick with its arrow pointing towards the
far end.**  If the cell of the row beyond `z` is the first cell of a stick of direction `u + 5`,
then `z` is either again the first cell of such a stick, or the last cell of a horizontal
stick -- the far end of the second stack above. -/
lemma top_step_five (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hpn : T.idx p < n)
    (hd' : T.dir (nbr (nbr p u) (u + 5)) = u + 5)
    (hi' : T.idx (nbr (nbr p u) (u + 5)) = 1) :
    (2 ≤ T.idx p ∧ T.dir (nbr p (u + 5)) = u + 5 ∧ T.idx (nbr p (u + 5)) = 1) ∨
      (T.dir (nbr p (u + 5)) = u ∧ T.idx (nbr p (u + 5)) = n) := by
  have hpos := T.idx_pos p
  set z := nbr p (u + 5) with hz
  set z' := nbr (nbr p u) (u + 5) with hz'
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  have hzz' : nbr z u = z' := by rw [hz, hz']; exact nbr_comm p (u + 5) u
  have hdpu : T.dir (nbr p u) = u := by
    have := T.succ_dir p hpn; rwa [hdp] at this
  have hipu : T.idx (nbr p u) = T.idx p + 1 := by
    have := T.succ_idx p hpn; rwa [hdp] at this
  have hA : T.label p (u + 5) = some (.a (T.idx p)) := by
    rw [T.label_shift5 (u := u) (k := 0) (by rw [hdp, add_zero])
      (by decide : (5 : HexDir) = 0 + 5), if_neg (by omega)]
  have hAface : ∀ Q, T.label z (u + 2) = some Q → ¬ Forbidden n (.a (T.idx p)) Q :=
    fun Q hQ hf => T.clash hv hA (by rw [opp_add_five]; exact hQ) hf
  have hAnone : T.label z (u + 2) ≠ none := fun h =>
    T.no_none hA (by rw [opp_add_five]; exact h)
  have hBnbr : nbr (nbr p u) (u + 4) = z := nbr_nbr_of_vec p (vec_zero_four u)
  have hB : T.label (nbr p u) (u + 4) = some (.b (T.idx p)) := by
    rw [T.label_shift4 (u := u) (k := 0) (by rw [hdpu, add_zero])
      (by decide : (4 : HexDir) = 0 + 4), if_neg (by omega), hipu]
    simp
  have hBface : ∀ Q, T.label z (u + 1) = some Q → ¬ Forbidden n (.b (T.idx p)) Q :=
    fun Q hQ hf => T.clash hv hB (by rw [hBnbr, opp_add_four]; exact hQ) hf
  have hBnone : T.label z (u + 1) ≠ none := fun h =>
    T.no_none hB (by rw [hBnbr, opp_add_four]; exact h)
  have hZnbr : nbr z' (u + 3) = z := by
    rw [← hzz']; exact nbr_nbr_cancel z (opp_eq_add_three u).symm
  have hZ : T.label z' (u + 3) = some .z1 := by
    rw [T.label_shift4 (u := u) (k := 5) (j := 3) hd' (by decide : (3 : HexDir) = 5 + 4),
      if_pos hi']
  have hZface : ∀ Q, T.label z (u + 0) = some Q → ¬ Forbidden n .z1 Q := fun Q hQ hf =>
    T.clash hv hZ (by rw [hZnbr, opp_add_three']; exact hQ) hf
  have hZnone : T.label z (u + 0) ≠ none := fun h =>
    T.no_none hZ (by rw [hZnbr, opp_add_three']; exact h)
  rcases hexDir_cases u (T.dir z) with hk | hk | hk | hk | hk | hk
  · -- `z` is the far end of a horizontal stick
    have hd0 : T.dir z = u + 0 := by rw [hk, add_zero]
    refine Or.inr ⟨hk, ?_⟩
    by_contra hi
    exact hZnone (by rw [T.label_shift0 (u := u) (k := 0) (j := 0) hd0 rfl, if_neg hi])
  · exfalso
    have hi : T.idx z ≠ n := by
      intro hi
      exact hZface .x2 (by rw [T.label_shift5 (u := u) (k := 1) (j := 0) hk
        (by decide : (0 : HexDir) = 1 + 5), if_pos hi])
        (Or.inr (ForbiddenCore.rule4 (Or.inr rfl) (Or.inl rfl)))
    exact hBnone (by rw [T.label_shift0 (u := u) (k := 1) (j := 1) hk rfl, if_neg hi])
  · exfalso
    by_cases hi : T.idx z = 1
    · exact hZface .z1 (by rw [T.label_shift4 (u := u) (k := 2) (j := 0) hk
        (by decide : (0 : HexDir) = 2 + 4), if_pos hi])
        (Or.inl (ForbiddenCore.rule2z (Or.inl rfl) (Or.inl rfl)))
    · exact hZface (.b (T.idx z - 1)) (by rw [T.label_shift4 (u := u) (k := 2) (j := 0) hk
        (by decide : (0 : HexDir) = 2 + 4), if_neg hi])
        (Or.inl (ForbiddenCore.rule9 (by omega) (by omega)))
  · exfalso
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hZnone (by rw [T.label_shift3 (u := u) (k := 3) (j := 0)
        (by rw [hk]) (by decide : (0 : HexDir) = 3 + 3), if_neg hi])
    exact hBface .z1 (by rw [T.label_shift4 (u := u) (k := 3) (j := 1) hk
      (by decide : (1 : HexDir) = 3 + 4), if_pos hi])
      (Or.inr (ForbiddenCore.rule9 (by omega) (by omega)))
  · exfalso
    have hi : T.idx z ≠ 1 := by
      intro hi
      exact hZface .x1 (by rw [T.label_shift2 (u := u) (k := 4) (j := 0) hk
        (by decide : (0 : HexDir) = 4 + 2), if_pos hi])
        (Or.inr (ForbiddenCore.rule4 (Or.inl rfl) (Or.inl rfl)))
    exact hBnone (by rw [T.label_shift3 (u := u) (k := 4) (j := 1) hk
      (by decide : (1 : HexDir) = 4 + 3), if_neg hi])
  · -- `z` is again the first cell of a stick of direction `u + 5`
    have hin : T.idx z ≠ n := by
      intro hi
      exact hZface .z2 (by rw [T.label_shift1 (u := u) (k := 5) (j := 0) hk
        (by decide : (0 : HexDir) = 5 + 1), if_pos hi])
        (Or.inl (ForbiddenCore.rule2z (Or.inl rfl) (Or.inr rfl)))
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hAnone (by rw [T.label_shift3 (u := u) (k := 5) (j := 2) hk
        (by decide : (2 : HexDir) = 5 + 3), if_neg hi])
    refine Or.inl ⟨?_, hk, hi⟩
    by_contra hp1
    have hp1' : T.idx p = 1 := by omega
    exact hAface .y1 (by rw [T.label_shift3 (u := u) (k := 5) (j := 2) hk
      (by decide : (2 : HexDir) = 5 + 3), if_pos hi])
      (by rw [hp1']; exact Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inl rfl)))

end StickTiling

end StickPolyhex
