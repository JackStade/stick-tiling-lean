import Tiling.Proofs.TopRow

/-!
# The row of cells below a left-leaning stack

Mirror image of `Tiling/Proofs/TopRow.lean`: the cells lying on the front side of the bottom
stick of a left-leaning stack are covered, from the near end towards the far end, first by the
horizontal stick filling the space beyond the near end, then by the left-slanting sticks of a
vertical stack, and finally by a second horizontal stick.

Throughout, `p` is a cell of the bottom stick of the stack, of direction `u`, and
`z = nbr p (u + 2)` is the cell of the row sitting below it; the cell of the row one step back
towards the near end is `nbr z (u + 3) = nbr (nbr p (u + 3)) (u + 2)`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- Common set-up of the three steps of the analysis of the row below a stack: the labels
presented to the cell `z = nbr p (u + 2)` by the two cells of the stick of `p` above it. -/
private lemma bot_row_faces (hv : T.SatisfiesWeaveRules) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hp2 : 2 ≤ T.idx p) :
    (∀ Q, T.label (nbr p (u + 2)) (u + 5) = some Q →
        ¬ Forbidden n (.c (n + 1 - T.idx p)) Q) ∧
      T.label (nbr p (u + 2)) (u + 5) ≠ none ∧
      (∀ Q, T.label (nbr p (u + 2)) (u + 4) = some Q →
        ¬ Forbidden n (.d (n + 1 - T.idx p)) Q) ∧
      T.label (nbr p (u + 2)) (u + 4) ≠ none := by
  have hle := T.idx_le p
  set z := nbr p (u + 2) with hz
  have hC : T.label p (u + 2) = some (.c (n + 1 - T.idx p)) := by
    rw [T.label_shift2 (u := u) (k := 0) (j := 2) (by rw [hdp, add_zero])
      (by decide : (2 : HexDir) = 0 + 2), if_neg (by omega)]
  have hpre_d : T.dir (nbr p (u + 3)) = u := by
    have := T.pred_dir p (by omega)
    rwa [hdp, opp_eq_add_three] at this
  have hpre_i : T.idx (nbr p (u + 3)) = T.idx p - 1 := by
    have := T.pred_idx p (by omega)
    rwa [hdp, opp_eq_add_three] at this
  have hDnbr : nbr (nbr p (u + 3)) (u + 1) = z := nbr_nbr_of_vec p (vec_three_one u)
  have hD : T.label (nbr p (u + 3)) (u + 1) = some (.d (n + 1 - T.idx p)) := by
    rw [T.label_shift1 (u := u) (k := 0) (j := 1) (by rw [hpre_d, add_zero])
      (by decide : (1 : HexDir) = 0 + 1), if_neg (by omega), hpre_i]
    congr 2
    omega
  refine ⟨fun Q hQ hf => T.clash hv hC (by rw [opp_add_two]; exact hQ) hf,
    fun h => T.no_none hC (by rw [opp_add_two]; exact h),
    fun Q hQ hf => T.clash hv hD (by rw [hDnbr, opp_add_one]; exact hQ) hf,
    fun h => T.no_none hD (by rw [hDnbr, opp_add_one]; exact h)⟩

/-- **Step of the analysis of the row below a stack, past a left-slanting stick with its arrow
pointing towards the far end.**  If the cell of the row before `z` (towards the near end of the
stack) is the first cell of a stick of direction `u + 2`, then `z` is either the first cell of a
horizontal stick -- the near end of the second stack below -- or again the first cell of a stick
of direction `u + 2`. -/
lemma bot_step_two (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hp3 : 3 ≤ T.idx p)
    (hd' : T.dir (nbr (nbr p (u + 3)) (u + 2)) = u + 2)
    (hi' : T.idx (nbr (nbr p (u + 3)) (u + 2)) = 1) :
    (T.dir (nbr p (u + 2)) = u ∧ T.idx (nbr p (u + 2)) = 1) ∨
      (T.dir (nbr p (u + 2)) = u + 2 ∧ T.idx (nbr p (u + 2)) = 1 ∧ T.idx p < n) := by
  have hle := T.idx_le p
  obtain ⟨hCface, hCnone, hDface, hDnone⟩ := T.bot_row_faces hv hdp (by omega)
  set z := nbr p (u + 2) with hz
  set z' := nbr (nbr p (u + 3)) (u + 2) with hz'
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  have hzz' : nbr z (u + 3) = z' := by rw [hz, hz']; exact nbr_comm p (u + 2) (u + 3)
  have hPnbr : nbr z' (u + 0) = z := by
    rw [← hzz', add_zero]; exact nbr_nbr_cancel z (opp_add_three u).symm
  have hP : T.label z' (u + 0) = some .z1 := by
    rw [T.label_shift4 (u := u) (k := 2) (j := 0) hd' (by decide : (0 : HexDir) = 2 + 4),
      if_pos hi']
  have hPface : ∀ Q, T.label z (u + 3) = some Q → ¬ Forbidden n .z1 Q := fun Q hQ hf =>
    T.clash hv hP (by rw [hPnbr, opp_add_zero']; exact hQ) hf
  have hPnone : T.label z (u + 3) ≠ none := fun h =>
    T.no_none hP (by rw [hPnbr, opp_add_zero']; exact h)
  rcases hexDir_cases u (T.dir z) with hk | hk | hk | hk | hk | hk
  · -- `z` is the near end of a horizontal stick
    have hd0 : T.dir z = u + 0 := by rw [hk, add_zero]
    refine Or.inl ⟨hk, ?_⟩
    by_contra hi
    exact hPnone (by rw [T.label_shift3 (u := u) (k := 0) (j := 3) hd0
      (by decide : (3 : HexDir) = 0 + 3), if_neg hi])
  · exfalso
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hDnone (by rw [T.label_shift3 (u := u) (k := 1) (j := 4) hk
        (by decide : (4 : HexDir) = 1 + 3), if_neg hi])
    exact hPface .x1 (by rw [T.label_shift2 (u := u) (k := 1) (j := 3) hk
      (by decide : (3 : HexDir) = 1 + 2), if_pos hi])
      (Or.inr (ForbiddenCore.rule4 (Or.inl rfl) (Or.inl rfl)))
  · -- `z` is again the first cell of a stick of direction `u + 2`
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hCnone (by rw [T.label_shift3 (u := u) (k := 2) (j := 5) hk
        (by decide : (5 : HexDir) = 2 + 3), if_neg hi])
    refine Or.inr ⟨hk, hi, ?_⟩
    by_contra hpn
    have hpn' : T.idx p = n := by omega
    exact hCface .y1 (by rw [T.label_shift3 (u := u) (k := 2) (j := 5) hk
      (by decide : (5 : HexDir) = 2 + 3), if_pos hi])
      (by rw [hpn', show n + 1 - n = 1 from by omega]
          exact Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inr rfl)))
  · exfalso
    have hi : T.idx z = n := by
      by_contra hi
      exact hPnone (by rw [T.label_shift0 (u := u) (k := 3) (j := 3) hk rfl, if_neg hi])
    exact hDface .z2 (by rw [T.label_shift1 (u := u) (k := 3) (j := 4) hk
      (by decide : (4 : HexDir) = 3 + 1), if_pos hi])
      (Or.inr (ForbiddenCore.rule7 (by omega) (by omega)))
  · exfalso
    have hi : T.idx z = n := by
      by_contra hi
      exact hDnone (by rw [T.label_shift0 (u := u) (k := 4) (j := 4) hk rfl, if_neg hi])
    exact hPface .x2 (by rw [T.label_shift5 (u := u) (k := 4) (j := 3) hk
      (by decide : (3 : HexDir) = 4 + 5), if_pos hi])
      (Or.inr (ForbiddenCore.rule4 (Or.inr rfl) (Or.inl rfl)))
  · exfalso
    have hi : T.idx z = n := by
      by_contra hi
      exact hCnone (by rw [T.label_shift0 (u := u) (k := 5) (j := 5) hk rfl, if_neg hi])
    exact hPface (.b (T.idx z - 1)) (by rw [T.label_shift4 (u := u) (k := 5) (j := 3) hk
      (by decide : (3 : HexDir) = 5 + 4), if_neg (by omega)])
      (Or.inl (ForbiddenCore.rule9 (by omega) (by omega)))

/-- **Step of the analysis of the row below a stack, past a left-slanting stick with its arrow
pointing towards the near end.**  If the cell of the row before `z` is the last cell of a stick
of direction `u + 5`, then `z` is the end of a left-slanting stick as well. -/
lemma bot_step_five (hv : T.SatisfiesWeaveRules) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hp2 : 2 ≤ T.idx p)
    (hd' : T.dir (nbr (nbr p (u + 3)) (u + 2)) = u + 5)
    (hi' : T.idx (nbr (nbr p (u + 3)) (u + 2)) = n) :
    T.idx p < n ∧
      ((T.dir (nbr p (u + 2)) = u + 2 ∧ T.idx (nbr p (u + 2)) = 1) ∨
        (T.dir (nbr p (u + 2)) = u + 5 ∧ T.idx (nbr p (u + 2)) = n)) := by
  have hle := T.idx_le p
  obtain ⟨hCface, hCnone, hDface, hDnone⟩ := T.bot_row_faces hv hdp hp2
  set z := nbr p (u + 2) with hz
  set z' := nbr (nbr p (u + 3)) (u + 2) with hz'
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  have hzz' : nbr z (u + 3) = z' := by rw [hz, hz']; exact nbr_comm p (u + 2) (u + 3)
  have hPnbr : nbr z' (u + 0) = z := by
    rw [← hzz', add_zero]; exact nbr_nbr_cancel z (opp_add_three u).symm
  have hP : T.label z' (u + 0) = some .z2 := by
    rw [T.label_shift1 (u := u) (k := 5) (j := 0) hd' (by decide : (0 : HexDir) = 5 + 1),
      if_pos hi']
  have hPface : ∀ Q, T.label z (u + 3) = some Q → ¬ Forbidden n .z2 Q := fun Q hQ hf =>
    T.clash hv hP (by rw [hPnbr, opp_add_zero']; exact hQ) hf
  have hPnone : T.label z (u + 3) ≠ none := fun h =>
    T.no_none hP (by rw [hPnbr, opp_add_zero']; exact h)
  rcases hexDir_cases u (T.dir z) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir z = u + 0 := by rw [hk, add_zero]
    by_cases hi : T.idx z = 1
    · exact hPface .y1 (by rw [T.label_shift3 (u := u) (k := 0) (j := 3) hd0
        (by decide : (3 : HexDir) = 0 + 3), if_pos hi])
        (Or.inr (ForbiddenCore.rule10 (Or.inl rfl)))
    · exact hPnone (by rw [T.label_shift3 (u := u) (k := 0) (j := 3) hd0
        (by decide : (3 : HexDir) = 0 + 3), if_neg hi])
  · exfalso
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hDnone (by rw [T.label_shift3 (u := u) (k := 1) (j := 4) hk
        (by decide : (4 : HexDir) = 1 + 3), if_neg hi])
    exact hPface .x1 (by rw [T.label_shift2 (u := u) (k := 1) (j := 3) hk
      (by decide : (3 : HexDir) = 1 + 2), if_pos hi])
      (Or.inr (ForbiddenCore.rule4 (Or.inl rfl) (Or.inr rfl)))
  · -- `z` is the first cell of a stick of direction `u + 2`
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hCnone (by rw [T.label_shift3 (u := u) (k := 2) (j := 5) hk
        (by decide : (5 : HexDir) = 2 + 3), if_neg hi])
    refine ⟨?_, Or.inl ⟨hk, hi⟩⟩
    by_contra hpn
    have hpn' : T.idx p = n := by omega
    exact hCface .y1 (by rw [T.label_shift3 (u := u) (k := 2) (j := 5) hk
      (by decide : (5 : HexDir) = 2 + 3), if_pos hi])
      (by rw [hpn', show n + 1 - n = 1 from by omega]
          exact Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inr rfl)))
  · exfalso
    by_cases hi : T.idx z = n
    · exact hPface .y2 (by rw [T.label_shift0 (u := u) (k := 3) (j := 3) hk rfl, if_pos hi])
        (Or.inr (ForbiddenCore.rule10 (Or.inr rfl)))
    · exact hPnone (by rw [T.label_shift0 (u := u) (k := 3) (j := 3) hk rfl, if_neg hi])
  · exfalso
    have hi : T.idx z = n := by
      by_contra hi
      exact hDnone (by rw [T.label_shift0 (u := u) (k := 4) (j := 4) hk rfl, if_neg hi])
    exact hPface .x2 (by rw [T.label_shift5 (u := u) (k := 4) (j := 3) hk
      (by decide : (3 : HexDir) = 4 + 5), if_pos hi])
      (Or.inr (ForbiddenCore.rule4 (Or.inr rfl) (Or.inr rfl)))
  · -- `z` is again the last cell of a stick of direction `u + 5`
    have hi : T.idx z = n := by
      by_contra hi
      exact hCnone (by rw [T.label_shift0 (u := u) (k := 5) (j := 5) hk rfl, if_neg hi])
    refine ⟨?_, Or.inr ⟨hk, hi⟩⟩
    by_contra hpn
    have hpn' : T.idx p = n := by omega
    exact hCface .y2 (by rw [T.label_shift0 (u := u) (k := 5) (j := 5) hk rfl, if_pos hi])
      (by rw [hpn', show n + 1 - n = 1 from by omega]
          exact Or.inr (ForbiddenCore.rule5 (Or.inr rfl) (Or.inr rfl)))

/-- **First step of the analysis of the row below a stack.**  The cell of the row just beyond
the far end of the horizontal stick filling the space beyond the near end of the stack is the
last cell of a left-slanting stick of direction `u + 5`. -/
lemma bot_step_tail (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {u : HexDir} {p : Hex}
    (hdp : T.dir p = u) (hp2 : 2 ≤ T.idx p)
    (hd' : T.dir (nbr (nbr p (u + 3)) (u + 2)) = u)
    (hi' : T.idx (nbr (nbr p (u + 3)) (u + 2)) = n) :
    T.idx p < n ∧ T.dir (nbr p (u + 2)) = u + 5 ∧ T.idx (nbr p (u + 2)) = n := by
  have hle := T.idx_le p
  obtain ⟨hCface, hCnone, hDface, hDnone⟩ := T.bot_row_faces hv hdp hp2
  set z := nbr p (u + 2) with hz
  set z' := nbr (nbr p (u + 3)) (u + 2) with hz'
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  have hzz' : nbr z (u + 3) = z' := by rw [hz, hz']; exact nbr_comm p (u + 2) (u + 3)
  have hPnbr : nbr z' (u + 0) = z := by
    rw [← hzz', add_zero]; exact nbr_nbr_cancel z (opp_add_three u).symm
  have hP : T.label z' (u + 0) = some .y2 := by
    rw [T.label_shift0 (u := u) (k := 0) (j := 0) (by rw [hd', add_zero]) rfl, if_pos hi']
  have hPface : ∀ Q, T.label z (u + 3) = some Q → ¬ Forbidden n .y2 Q := fun Q hQ hf =>
    T.clash hv hP (by rw [hPnbr, opp_add_zero']; exact hQ) hf
  have hPnone : T.label z (u + 3) ≠ none := fun h =>
    T.no_none hP (by rw [hPnbr, opp_add_zero']; exact h)
  rcases hexDir_cases u (T.dir z) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir z = u + 0 := by rw [hk, add_zero]
    by_cases hi : T.idx z = 1
    · exact hPface .y1 (by rw [T.label_shift3 (u := u) (k := 0) (j := 3) hd0
        (by decide : (3 : HexDir) = 0 + 3), if_pos hi])
        (Or.inl (ForbiddenCore.rule1 (Or.inr rfl) (Or.inl rfl)))
    · exact hPnone (by rw [T.label_shift3 (u := u) (k := 0) (j := 3) hd0
        (by decide : (3 : HexDir) = 0 + 3), if_neg hi])
  · exfalso
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hDnone (by rw [T.label_shift3 (u := u) (k := 1) (j := 4) hk
        (by decide : (4 : HexDir) = 1 + 3), if_neg hi])
    exact hPface .x1 (by rw [T.label_shift2 (u := u) (k := 1) (j := 3) hk
      (by decide : (3 : HexDir) = 1 + 2), if_pos hi])
      (Or.inl (ForbiddenCore.rule3 (Or.inr rfl) (Or.inl rfl)))
  · exfalso
    have hi : T.idx z = 1 := by
      by_contra hi
      exact hCnone (by rw [T.label_shift3 (u := u) (k := 2) (j := 5) hk
        (by decide : (5 : HexDir) = 2 + 3), if_neg hi])
    exact hPface (.d (n - T.idx z)) (by rw [T.label_shift1 (u := u) (k := 2) (j := 3) hk
      (by decide : (3 : HexDir) = 2 + 1), if_neg (by omega)])
      (by rw [hi]; exact Or.inl (ForbiddenCore.rule11 (Or.inr rfl)))
  · exfalso
    by_cases hi : T.idx z = n
    · exact hPface .y2 (by rw [T.label_shift0 (u := u) (k := 3) (j := 3) hk rfl, if_pos hi])
        (Or.inl (ForbiddenCore.rule1 (Or.inr rfl) (Or.inr rfl)))
    · exact hPnone (by rw [T.label_shift0 (u := u) (k := 3) (j := 3) hk rfl, if_neg hi])
  · exfalso
    have hi : T.idx z = n := by
      by_contra hi
      exact hDnone (by rw [T.label_shift0 (u := u) (k := 4) (j := 4) hk rfl, if_neg hi])
    exact hPface .x2 (by rw [T.label_shift5 (u := u) (k := 4) (j := 3) hk
      (by decide : (3 : HexDir) = 4 + 5), if_pos hi])
      (Or.inl (ForbiddenCore.rule3 (Or.inr rfl) (Or.inr rfl)))
  · -- `z` is the last cell of a left-slanting stick of direction `u + 5`
    have hi : T.idx z = n := by
      by_contra hi
      exact hCnone (by rw [T.label_shift0 (u := u) (k := 5) (j := 5) hk rfl, if_neg hi])
    refine ⟨?_, hk, hi⟩
    by_contra hpn
    have hpn' : T.idx p = n := by omega
    exact hCface .y2 (by rw [T.label_shift0 (u := u) (k := 5) (j := 5) hk rfl, if_pos hi])
      (by rw [hpn', show n + 1 - n = 1 from by omega]
          exact Or.inr (ForbiddenCore.rule5 (Or.inr rfl) (Or.inr rfl)))

end StickTiling

end StickPolyhex
