import Tiling.Proofs.WeaveUp

/-!
# Propagating a left-leaning stack diagonally, on the front side

This file is the mirror image of `Tiling/Proofs/WeaveUp.lean`: it carries the analysis of the
space `B` of the paper, diagonally beyond the *near* ends of the sticks of a left-leaning stack,
and shows that the horizontal stick filling that space is again part of a left-leaning stack,
which is a *different* stack, lying below the given one.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### The stick beyond the far end of the new horizontal stick -/

/-- **The cell beyond the far end of the new horizontal stick is the near end of a left-slanting
stick.**  Here `x` is a stick of a left-leaning stack of direction `u`, and the cell `B`
diagonally beyond its near end is an interior cell of a new horizontal stick, whose far end is
`T.tail B`. -/
theorem dir_westCell_tail_of_frontCorner (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (hdB : T.dir (nbr (T.head x) (u + 2)) = u)
    (hj1 : 1 < T.idx (nbr (T.head x) (u + 2))) (hjn : T.idx (nbr (T.head x) (u + 2)) < n) :
    T.dir (nbr (T.tail (nbr (T.head x) (u + 2))) u) = u + 5 ∧
      T.idx (nbr (T.tail (nbr (T.head x) (u + 2))) u) = n := by
  have h0n : 0 < n := by omega
  set H := T.head x with hH
  set B := nbr H (u + 2) with hB
  set j := T.idx B with hj
  set K := T.tail B with hK
  set Rw := nbr K u with hRw
  have hdH : T.dir H = u := by
    rw [hH, T.dir_head x, T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have hiH : T.idx H = 1 := T.idx_head x
  have hdK : T.dir K = u := by rw [hK, T.dir_tail h0n B, hdB]
  have hiK : T.idx K = n := T.idx_tail h0n B
  have hjle : j ≤ n := T.idx_le B
  -- the two cells of the stack lying above the far end of the new stick
  have hq := T.dir_walk_forward H (n - j) (by rw [hiH]; omega)
  have hq2 := T.dir_walk_forward H (n - j + 1) (by rw [hiH]; omega)
  rw [hdH] at hq hq2
  set q := walk H u ((n - j : ℕ) : ℤ) with hqdef
  set q2 := walk H u ((n - j + 1 : ℕ) : ℤ) with hq2def
  have hdq : T.dir q = u := hq.1
  have hiq : T.idx q = n - j + 1 := by rw [hq.2, hiH]; omega
  have hdq2 : T.dir q2 = u := hq2.1
  have hiq2 : T.idx q2 = n - j + 2 := by rw [hq2.2, hiH]; omega
  -- geometry
  have hKeq : K = nbr q (u + 2) := by
    rw [hK, T.tail_eq_walk h0n, hdB, hqdef, hB, ← hj,
      show ((n : ℤ) - j) = ((n - j : ℕ) : ℤ) from by omega]
    simp only [walk, nbr]
    abel
  have hRwq : nbr q (u + 1) = Rw := by
    rw [hRw, hKeq]
    simp only [nbr]
    rw [(by decide : ∀ a : HexDir, (a + 1).vec = (a + 2).vec + a.vec) u]
    abel
  have hRwq2 : nbr q2 (u + 2) = Rw := by
    rw [hRw, hKeq, hq2def, hqdef, show ((n - j + 1 : ℕ) : ℤ) = ((n - j : ℕ) : ℤ) + 1 from by omega]
    simp only [walk, nbr, add_smul, one_smul]
    abel
  -- the three labels presented to `Rw`
  have hy2 : T.label K u = some .y2 := by
    rw [← hdK, T.label_dir, if_pos hiK]
  have hd1 : T.label q (u + 1) = some (.d (j - 1)) := by
    rw [T.label_shift1 (u := u) (k := 0) (j := 1) (by rw [hdq, add_zero])
      (by decide : (1 : HexDir) = 0 + 1), if_neg (by omega), hiq,
      show n - (n - j + 1) = j - 1 from by omega]
  have hc1 : T.label q2 (u + 2) = some (.c (j - 1)) := by
    rw [T.label_shift2 (u := u) (k := 0) (j := 2) (by rw [hdq2, add_zero])
      (by decide : (2 : HexDir) = 0 + 2), if_neg (by omega), hiq2,
      show n + 1 - (n - j + 2) = j - 1 from by omega]
  have hfaceY : ∀ Q, T.label Rw (u + 3) = some Q → ¬ Forbidden n .y2 Q := fun Q hQ hf =>
    T.clash hv hy2 (by rw [← hRw, opp_eq_add_three]; exact hQ) hf
  have hnoneY : T.label Rw (u + 3) ≠ none := fun h =>
    T.no_none hy2 (by rw [← hRw, opp_eq_add_three]; exact h)
  have hfaceD : ∀ Q, T.label Rw (u + 4) = some Q → ¬ Forbidden n (.d (j - 1)) Q := fun Q hQ hf =>
    T.clash hv hd1 (by rw [hRwq, opp_add_one]; exact hQ) hf
  have hnoneD : T.label Rw (u + 4) ≠ none := fun h =>
    T.no_none hd1 (by rw [hRwq, opp_add_one]; exact h)
  have hfaceC : ∀ Q, T.label Rw (u + 5) = some Q → ¬ Forbidden n (.c (j - 1)) Q := fun Q hQ hf =>
    T.clash hv hc1 (by rw [hRwq2, opp_add_two]; exact hQ) hf
  have hnoneC : T.label Rw (u + 5) ≠ none := fun h =>
    T.no_none hc1 (by rw [hRwq2, opp_add_two]; exact h)
  have hposR := T.idx_pos Rw
  have hleR := T.idx_le Rw
  rcases hexDir_cases u (T.dir Rw) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir Rw = u + 0 := by rw [hk, add_zero]
    by_cases hi1 : T.idx Rw = 1
    · exact hfaceY .y1 (by rw [T.label_shift3 hd0 (by decide : (3 : HexDir) = 0 + 3), if_pos hi1])
        (forbidden_of_isY_isY (Or.inr rfl) (Or.inl rfl))
    · exact hnoneY (by rw [T.label_shift3 hd0 (by decide : (3 : HexDir) = 0 + 3), if_neg hi1])
  · exfalso
    by_cases hi1 : T.idx Rw = 1
    · exact hfaceY .x1 (by rw [T.label_shift2 hk (by decide : (3 : HexDir) = 1 + 2), if_pos hi1])
        (Or.inl (ForbiddenCore.rule3 (Or.inr rfl) (Or.inl rfl)))
    · exact hnoneD (by rw [T.label_shift3 hk (by decide : (4 : HexDir) = 1 + 3), if_neg hi1])
  · exfalso
    by_cases hin : T.idx Rw = n
    · exact hfaceY .z2 (by rw [T.label_shift1 hk (by decide : (3 : HexDir) = 2 + 1), if_pos hin])
        (Or.inl (ForbiddenCore.rule10 (Or.inr rfl)))
    · by_cases hi1 : T.idx Rw = 1
      · refine hfaceY (.d (n - 1)) ?_ (Or.inl (ForbiddenCore.rule11 (Or.inr rfl)))
        rw [T.label_shift1 hk (by decide : (3 : HexDir) = 2 + 1), if_neg hin, hi1]
      · exact hnoneC (by rw [T.label_shift3 hk (by decide : (5 : HexDir) = 2 + 3), if_neg hi1])
  · exfalso
    by_cases hin : T.idx Rw = n
    · exact hfaceY .y2 (by rw [T.label_shift0 hk (by decide : (3 : HexDir) = 3), if_pos hin])
        (forbidden_of_isY_isY (Or.inr rfl) (Or.inr rfl))
    · exact hnoneY (by rw [T.label_shift0 hk (by decide : (3 : HexDir) = 3), if_neg hin])
  · exfalso
    by_cases hin : T.idx Rw = n
    · exact hfaceY .x2 (by rw [T.label_shift5 hk (by decide : (3 : HexDir) = 4 + 5), if_pos hin])
        (Or.inl (ForbiddenCore.rule3 (Or.inr rfl) (Or.inr rfl)))
    · by_cases hi1 : T.idx Rw = 1
      · refine hfaceY (.a 1) ?_ (Or.inl (ForbiddenCore.rule5 (Or.inr rfl) (Or.inl rfl)))
        rw [T.label_shift5 hk (by decide : (3 : HexDir) = 4 + 5), if_neg hin, hi1]
      · exact hnoneD (by rw [T.label_shift0 hk (by decide : (4 : HexDir) = 4), if_neg hin])
  · refine ⟨hk, ?_⟩
    by_contra hin
    exact hnoneC (by rw [T.label_shift0 hk (by decide : (5 : HexDir) = 5), if_neg hin])

/-! ### The new horizontal stick is part of a left-leaning stack -/

/-- **Every left-leaning stack has a left-leaning stack diagonally beyond its near ends.**  Let
`x` be a stick of a left-leaning stack of direction `u`.  The cell diagonally beyond the near
end of `x`, on its front side, either belongs to the same stack, or it belongs to a *new*
left-leaning stack of horizontal sticks. -/
theorem isLeftLeaningStack_frontCorner (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x) :
    T.SameStack c (nbr (T.head x) (u + 2)) ∨
      T.IsLeftLeaningStack (nbr (T.head x) (u + 2)) := by
  have h0n : 0 < n := by omega
  obtain ⟨hdB, hcase⟩ := T.dir_frontCorner_beyond_head hv (by omega) hL hu hx
  rcases hcase with ⟨_, hsame⟩ | ⟨hj1, hjn⟩
  · exact Or.inl hsame
  refine Or.inr ?_
  set B := nbr (T.head x) (u + 2) with hB
  set K := T.tail B with hK
  have hdK : T.dir K = u := by rw [hK, T.dir_tail h0n B, hdB]
  have hiK : T.idx K = n := T.idx_tail h0n B
  obtain ⟨hdRw, hiRw⟩ := T.dir_westCell_tail_of_frontCorner hv hn hL hu hx hdB hj1 hjn
  set Rw := nbr K u with hRw
  set g := nbr Rw (u + 2) with hg
  set w := nbr K (u + 2) with hw
  -- the cell of the left-slanting stick west of the new stick
  have hdg : T.dir g = u + 5 := by
    have h1 : nbr Rw (T.dir Rw).opp = g := by rw [hdRw, opp_add_five, hg]
    have h2 := T.pred_dir Rw (by omega)
    rw [h1, hdRw] at h2
    exact h2
  have hig : T.idx g = n - 1 := by
    have h1 : nbr Rw (T.dir Rw).opp = g := by rw [hdRw, opp_add_five, hg]
    have h2 := T.pred_idx Rw (by omega)
    rw [h1, hiRw] at h2
    exact h2
  have hgw : nbr w u = g := by
    rw [hw, hg, hRw]
    simp only [nbr]
    abel
  have hnextg : nbr w (u + 1) = nbr g (u + 2) := by
    rw [hw, hg, hRw]
    simp only [nbr]
    rw [(by decide : ∀ a : HexDir, (a + 1).vec = (a + 2).vec + a.vec) u]
    abel
  have hdnext : T.dir (nbr w (u + 1)) = u + 5 := by
    have h1 : nbr g (T.dir g).opp = nbr g (u + 2) := by rw [hdg, opp_add_five]
    have h2 := T.pred_dir g (by omega)
    rw [h1, hdg] at h2
    rw [hnextg]
    exact h2
  -- the cell of the stack just before the far end of the new stick
  have hdK' : T.dir (nbr K (u + 3)) = u := by
    have h1 : nbr K (T.dir K).opp = nbr K (u + 3) := by rw [hdK, opp_eq_add_three]
    have h2 := T.pred_dir K (by omega)
    rw [h1, hdK] at h2
    exact h2
  have hiK' : T.idx (nbr K (u + 3)) = n - 1 := by
    have h1 : nbr K (T.dir K).opp = nbr K (u + 3) := by rw [hdK, opp_eq_add_three]
    have h2 := T.pred_idx K (by omega)
    rw [h1, hiK] at h2
    exact h2
  have hKw : nbr (nbr K (u + 3)) (u + 1) = w := by
    rw [hw]
    simp only [nbr]
    rw [(by decide : ∀ a : HexDir, (a + 1).vec = (a + 2).vec + a.vec) u,
      (by decide : ∀ a : HexDir, (a + 3).vec = -a.vec) u]
    abel
  -- the three labels presented to the cell below the far end of the new stick
  have hc1 : T.label K (u + 2) = some (.c 1) := by
    rw [T.label_shift2 (u := u) (k := 0) (j := 2) (by rw [hdK, add_zero])
      (by decide : (2 : HexDir) = 0 + 2), if_neg (by omega), hiK,
      show n + 1 - n = 1 from by omega]
  have hd1 : T.label (nbr K (u + 3)) (u + 1) = some (.d 1) := by
    rw [T.label_shift1 (u := u) (k := 0) (j := 1) (by rw [hdK', add_zero])
      (by decide : (1 : HexDir) = 0 + 1), if_neg (by omega), hiK',
      show n - (n - 1) = 1 from by omega]
  have hbg : T.label g (u + 3) = some (.b (n - 2)) := by
    rw [T.label_shift4 (u := u) (k := 5) (j := 3) hdg (by decide : (3 : HexDir) = 5 + 4),
      if_neg (by omega), hig, show n - 1 - 1 = n - 2 from by omega]
  have hfaceC : ∀ Q, T.label w (u + 5) = some Q → ¬ Forbidden n (.c 1) Q := fun Q hQ hf =>
    T.clash hv hc1 (by rw [← hw, opp_add_two]; exact hQ) hf
  have hnoneC : T.label w (u + 5) ≠ none := fun h =>
    T.no_none hc1 (by rw [← hw, opp_add_two]; exact h)
  have hfaceD : ∀ Q, T.label w (u + 4) = some Q → ¬ Forbidden n (.d 1) Q := fun Q hQ hf =>
    T.clash hv hd1 (by rw [hKw, opp_add_one]; exact hQ) hf
  have hnoneD : T.label w (u + 4) ≠ none := fun h =>
    T.no_none hd1 (by rw [hKw, opp_add_one]; exact h)
  have hgw' : nbr g (u + 3) = w := by
    rw [← hgw]
    exact nbr_nbr_cancel w (opp_eq_add_three u).symm
  have hnoneB : T.label w (u + 0) ≠ none := fun h =>
    T.no_none hbg (by rw [hgw', opp_add_three']; exact h)
  have hposw := T.idx_pos w
  have hlew := T.idx_le w
  -- the cell below the far end of the new stick is the far end of a horizontal stick
  have hkey : T.dir w = u ∧ T.idx w = n := by
    rcases hexDir_cases u (T.dir w) with hk | hk | hk | hk | hk | hk
    · have hd0 : T.dir w = u + 0 := by rw [hk, add_zero]
      refine ⟨hk, ?_⟩
      by_contra hin
      exact hnoneB (by rw [T.label_shift0 hd0 (by decide : (0 : HexDir) = 0), if_neg hin])
    · exfalso
      have hi1 : T.idx w = 1 := by
        by_contra hi1
        exact hnoneD (by rw [T.label_shift3 hk (by decide : (4 : HexDir) = 1 + 3), if_neg hi1])
      have h1 : nbr w (T.dir w) = nbr w (u + 1) := by rw [hk]
      have h2 := T.succ_dir w (by omega)
      rw [h1, hk, hdnext] at h2
      exact (by decide : ∀ a : HexDir, a + 5 ≠ a + 1) u h2
    · exfalso
      by_cases hi1 : T.idx w = 1
      · exact hfaceC .y1 (by rw [T.label_shift3 hk (by decide : (5 : HexDir) = 2 + 3), if_pos hi1])
          (Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inr rfl)))
      · exact hnoneC (by rw [T.label_shift3 hk (by decide : (5 : HexDir) = 2 + 3), if_neg hi1])
    · exfalso
      by_cases hi1 : T.idx w = 1
      · exact hfaceC .x1 (by rw [T.label_shift2 hk (by decide : (5 : HexDir) = 3 + 2), if_pos hi1])
          (Or.inr (ForbiddenCore.rule6 (le_refl 1) (by omega)))
      · exact hnoneB (by rw [T.label_shift3 hk (by decide : (0 : HexDir) = 3 + 3), if_neg hi1])
    · exfalso
      have hin : T.idx w = n := by
        by_contra hin
        exact hnoneD (by rw [T.label_shift0 hk (by decide : (4 : HexDir) = 4), if_neg hin])
      have h1 : nbr w (T.dir w).opp = nbr w (u + 1) := by rw [hk, opp_add_four]
      have h2 := T.pred_dir w (by omega)
      rw [h1, hk, hdnext] at h2
      exact (by decide : ∀ a : HexDir, a + 5 ≠ a + 4) u h2
    · exfalso
      by_cases hin : T.idx w = n
      · exact hfaceC .y2 (by rw [T.label_shift0 hk (by decide : (5 : HexDir) = 5), if_pos hin])
          (Or.inr (ForbiddenCore.rule5 (Or.inr rfl) (Or.inr rfl)))
      · exact hnoneC (by rw [T.label_shift0 hk (by decide : (5 : HexDir) = 5), if_neg hin])
  -- the two horizontal sticks ending side by side form a left-leaning pair
  have hwK : nbr w (u + 5) = K := by
    rw [hw]
    exact nbr_nbr_cancel K (opp_add_two u).symm
  have hEw : T.EndsAt w (u + 5 + 1) := by
    refine Or.inl ⟨?_, hkey.2⟩
    rw [hkey.1, (by decide : ∀ a : HexDir, a + 5 + 1 = a) u]
  have hEK : T.EndsAt (nbr w (u + 5)) (u + 5 + 1) := by
    rw [hwK]
    refine Or.inl ⟨?_, hiK⟩
    rw [hdK, (by decide : ∀ a : HexDir, a + 5 + 1 = a) u]
  have hpair : T.LeansLeft w (nbr w (u + 5)) := T.leansLeft_of_endsAt_pair hEw hEK
  rw [hwK] at hpair
  refine ⟨K, w, ?_, T.leansLeft_symm hpair⟩
  exact T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n B)).symm

/-! ### A genuinely new stack below the near ends -/

/-- **Some stick of a left-leaning stack has the space `B` beyond its near end outside the
stack.**  Taking for `x` the stick of the stack whose near end sits at the very end of the stick
flanking the stack on the front side, the cell diagonally beyond the near end of `x` cannot
belong to the stack itself. -/
theorem exists_frontCorner_not_sameStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ x, T.SameStack c x ∧ ¬ T.SameStack c (nbr (T.head x) (u + 2)) := by
  have h0n : 0 < n := by omega
  have hne3 : u ≠ u + 3 := (by decide : ∀ a : HexDir, a ≠ a + 3) u
  have hax : SameAxis (u + 3) (T.dir c) := Or.inr (by rw [hu, opp_add_three])
  -- the stick flanking the near ends of the stack, and its own far end `y`
  have hdE : T.dir (nbr (T.head c) (u + 3)) = u + 2 := by
    have h2 := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl c)).2
    rwa [hu, opp_eq_add_three] at h2
  have hfc : T.frontCell (u + 3) c = nbr (T.head c) (u + 3) := by
    rw [frontCell, endCell, if_neg (by rw [hu]; exact hne3)]
  have hyE : T.tail (nbr (T.head c) (u + 3)) ∈ T.stickOf (nbr (T.head c) (u + 3)) :=
    T.tail_mem_stickOf h0n _
  have hdy : T.dir (T.tail (nbr (T.head c) (u + 3))) = u + 2 := by rw [T.dir_tail h0n, hdE]
  have hiy : T.idx (T.tail (nbr (T.head c) (u + 3))) = n := T.idx_tail h0n _
  obtain ⟨x, hx, hxy⟩ := T.exists_sameStack_frontCell_eq hv hn hL hax (by rw [hfc]; exact hyE)
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx, hu]
  rw [frontCell, endCell, if_neg (by rw [hdx]; exact hne3)] at hxy
  refine ⟨x, hx, fun hsame => ?_⟩
  have hdB : T.dir (nbr (T.head x) (u + 2)) = u :=
    (T.dir_frontCorner_beyond_head hv hn hL hu hx).1
  have hneB : T.dir (nbr (T.head x) (u + 2)) ≠ u + 3 := by rw [hdB]; exact hne3
  -- the cell beyond the near end of the new stick lies on the flanking stick
  have hmem : T.frontCell (u + 3) (nbr (T.head x) (u + 2)) ∈ T.stickOf (T.frontCell (u + 3) c) :=
    (T.frontCell_mem_of_sameStack hv h0n (d := u + 3) hax hsame).2
  rw [hfc, show T.frontCell (u + 3) (nbr (T.head x) (u + 2))
      = nbr (T.head (nbr (T.head x) (u + 2))) (u + 3) from by
    rw [frontCell, endCell, if_neg hneB]] at hmem
  -- both that cell and `y` lie on the flanking stick, so they differ by a multiple of `u + 2`
  obtain ⟨k, hk⟩ := T.exists_walk_of_mem_stickOf hmem hyE
  rw [hdE] at hk
  obtain ⟨m, hm⟩ : ∃ m : ℤ, -((T.idx (nbr (T.head x) (u + 2)) : ℤ) - 1) = m := ⟨_, rfl⟩
  have hheadB : T.head (nbr (T.head x) (u + 2)) = walk (nbr (T.head x) (u + 2)) u m := by
    rw [head, hdB, hm]
  have hk2 := hk
  rw [hheadB, ← hxy] at hk2
  have hkey : m • u.vec = (k - 1) • (u + 2).vec := by
    simp only [walk, nbr] at hk2
    linear_combination (norm := module) hk2
  obtain ⟨-, hk1⟩ := smul_vec_eq_smul_vec
    ((by decide : ∀ a : HexDir, a ≠ a + 2) u)
    (by rw [opp_add_two]; exact (by decide : ∀ a : HexDir, a ≠ a + 5) u) hkey
  -- so that cell is one step beyond the far end of the flanking stick, which is impossible
  rw [show k = 1 from by omega, ← nbr_eq_walk_one] at hk
  rw [hk, ← T.stickOf_eq_of_mem hyE] at hmem
  exact T.nbr_dir_not_mem_stickOf hiy (by rw [hdy]; exact hmem)

/-- **Every left-leaning stack has a left-leaning stack below it.**  A left-leaning stack of
horizontal sticks of direction `u` has, diagonally beyond its near ends, a *different*
left-leaning stack of horizontal sticks, again of direction `u`.  Together with
`exists_stackAbove_isLeftLeaningStack` this is the statement that every left-leaning stack has
left-leaning stacks on both of its sides. -/
theorem exists_stackBelow_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ c', T.dir c' = u ∧ T.IsLeftLeaningStack c' ∧ T.StackBelow u c c' := by
  obtain ⟨x, hx, hne⟩ := T.exists_frontCorner_not_sameStack hv (by omega) hL hu
  have hdB : T.dir (nbr (T.head x) (u + 2)) = u :=
    (T.dir_frontCorner_beyond_head hv (by omega) hL hu hx).1
  have hLB : T.IsLeftLeaningStack (nbr (T.head x) (u + 2)) := by
    rcases T.isLeftLeaningStack_frontCorner hv hn hL hu hx with h | h
    · exact absurd h hne
    · exact h
  refine ⟨nbr (T.head x) (u + 2), hdB, hLB, hne, T.head x, ?_, Or.inr (T.sameStack_refl _)⟩
  exact SameStack.trans T hx
    (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.head_mem_stickOf x)).symm)

/-! ### A block of the weave pattern with its neighbouring stacks -/

/-- **A block of the weave pattern together with a stack above it and a stack below it.**  Every
valid tiling by sticks of length at least `3` contains an oriented left-leaning stack of `n`
horizontal sticks of direction `u` which has, above it and below it, two further left-leaning
stacks of `n` horizontal sticks of the same direction `u`. -/
theorem exists_weave_neighbours_of_satisfiesWeaveRules (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) :
    ∃ (u : HexDir) (c : Hex), T.dir c = u ∧ T.IsLeftLeaningStack c ∧ T.stackHeight c = n ∧
      (∃ a, T.dir a = u ∧ T.IsLeftLeaningStack a ∧ T.stackHeight a = n ∧ T.StackAbove u c a) ∧
      (∃ b, T.dir b = u ∧ T.IsLeftLeaningStack b ∧ T.stackHeight b = n ∧ T.StackBelow u c b) := by
  obtain ⟨c, hL⟩ := T.exists_isLeftLeaningStack hv hn
  obtain ⟨a, hda, hLa, hAbove⟩ := T.exists_stackAbove_isLeftLeaningStack hv hn hL rfl
  obtain ⟨b, hdb, hLb, hBelow⟩ := T.exists_stackBelow_isLeftLeaningStack hv hn hL rfl
  exact ⟨T.dir c, c, rfl, hL, T.stackHeight_eq_of_isLeftLeaningStack hv (by omega) hL,
    ⟨a, hda, hLa, T.stackHeight_eq_of_isLeftLeaningStack hv (by omega) hLa, hAbove⟩,
    ⟨b, hdb, hLb, T.stackHeight_eq_of_isLeftLeaningStack hv (by omega) hLb, hBelow⟩⟩

end StickTiling

end StickPolyhex
