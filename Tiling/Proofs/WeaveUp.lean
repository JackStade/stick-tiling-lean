import Mathlib.Tactic.Module
import Tiling.Proofs.Weave

/-!
# Propagating a left-leaning stack diagonally

This file carries the proof of Lemma 4 one step further: the horizontal stick found diagonally
beyond the far end of a left-leaning stack (`StickTiling.dir_backCorner_beyond_tail`) is itself
part of a left-leaning stack.

The argument is the one of Figures 13 to 15 of the paper.  Write `u` for the direction of the
sticks of the stack, `t` for the far end (the tail) of one of them, and `A` for the cell
diagonally beyond `t`, on the back side.  If `A` is not the tail of the next stick up the stack,
then `A` lies on a new horizontal stick `T` which meets some, but not all, of the concave
corners on the back side of the stack, so that

* the head `H` of `T` sits above the stack, and the two cells `p`, `p'` of the stack below `H`
  and below the cell east of `H` present the labels `b` and `a` to that cell;
* consequently the cell `R` east of `H` is the far end of a left-slanting stick of direction
  `u + 2` (`StickTiling.dir_eastCell_head_of_backCorner`);
* the cell just above `H` is then forced to be the head of a horizontal stick, since the two
  alternatives allowed by `backCorner_head` would put a second direction on the cell north-east
  of `H`, which already belongs to the left-slanting stick through `R`;
* the two horizontal sticks ending side by side form a left-leaning pair
  (`StickTiling.isLeftLeaningStack_backCorner`).
-/

namespace StickPolyhex

/-! ### Two non-parallel directions are independent -/

/-- Two directions that are neither equal nor opposite span the plane: the determinant of their
translation vectors is nonzero. -/
lemma vec_det_ne_zero {d e : HexDir} (h1 : d ≠ e) (h2 : d ≠ e.opp) :
    d.vec.1 * e.vec.2 - d.vec.2 * e.vec.1 ≠ 0 := by
  revert h1 h2; revert d e; decide

/-- A multiple of the translation vector of `d` is a multiple of the translation vector of a
direction `e` other than `d` and its opposite only if both multiples vanish. -/
lemma smul_vec_eq_smul_vec {d e : HexDir} (hde : d ≠ e) (hde' : d ≠ e.opp) {a b : ℤ}
    (h : a • d.vec = b • e.vec) : a = 0 ∧ b = 0 := by
  have hdet := vec_det_ne_zero hde hde'
  have hf : a * d.vec.1 = b * e.vec.1 := by
    have := congrArg Prod.fst h; simpa using this
  have hs : a * d.vec.2 = b * e.vec.2 := by
    have := congrArg Prod.snd h; simpa using this
  have ha : a * (d.vec.1 * e.vec.2 - d.vec.2 * e.vec.1) = 0 := by
    linear_combination e.vec.2 * hf - e.vec.1 * hs
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 ha with h' | h'
    · exact h'
    · exact absurd h' hdet
  refine ⟨ha0, ?_⟩
  rw [ha0, zero_smul] at h
  rcases smul_eq_zero.1 h.symm with h' | h'
  · exact h'
  · exact absurd h' (HexDir.vec_ne_zero e)

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Two cells of one stick differ by a multiple of its direction -/

/-- Two cells of the same stick differ by a multiple of the direction of that stick. -/
lemma exists_walk_of_mem_stickOf {z p q : Hex} (hp : p ∈ T.stickOf z) (hq : q ∈ T.stickOf z) :
    ∃ k : ℤ, p = walk q (T.dir z) k := by
  rw [T.mem_stickOf_iff] at hp hq
  obtain ⟨kp, _, rfl⟩ := hp
  obtain ⟨kq, _, rfl⟩ := hq
  refine ⟨(kp : ℤ) - kq, ?_⟩
  simp only [cellOfStick, walk_walk]
  congr 1
  omega

/-- The far end of the stick through `c` is reached from `c` by `n - T.idx c` steps. -/
lemma tail_eq_walk (hn : 0 < n) (c : Hex) :
    T.tail c = walk c (T.dir c) ((n : ℤ) - T.idx c) := by
  have hpos := T.idx_pos c
  have hle := T.idx_le c
  simp only [tail, cellOfStick, head, walk_walk]
  congr 1
  omega

/-! ### The stick beyond the head of the new horizontal stick -/

/-- **The cell east of the head of the new horizontal stick is the far end of a left-slanting
stick.**  Here `x` is a stick of a left-leaning stack of direction `u`, and the cell `A`
diagonally beyond its far end is an interior cell of a new horizontal stick, whose head is
`T.head A`. -/
theorem dir_eastCell_head_of_backCorner (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (hdA : T.dir (nbr (T.tail x) (u + 5)) = u)
    (hi1 : 1 < T.idx (nbr (T.tail x) (u + 5))) (hin : T.idx (nbr (T.tail x) (u + 5)) < n) :
    T.dir (nbr (T.head (nbr (T.tail x) (u + 5))) (u + 3)) = u + 2 ∧
      T.idx (nbr (T.head (nbr (T.tail x) (u + 5))) (u + 3)) = n := by
  have h0n : 0 < n := by omega
  set t := T.tail x with ht
  set A := nbr t (u + 5) with hA
  set i := T.idx A with hi
  set H := T.head A with hH
  have hdH : T.dir H = u := by rw [hH, T.dir_head A, hdA]
  have hiH : T.idx H = 1 := T.idx_head A
  have hdt : T.dir t = u := by
    rw [ht, T.dir_tail h0n x,
      T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have hit : T.idx t = n := T.idx_tail h0n x
  -- the two cells of the stick of `x` below the new stick
  set p := walk t u (-((i : ℤ) - 1)) with hp
  set p2 := walk t u (-(i : ℤ)) with hp2
  set R := nbr H (u + 3) with hR
  -- direction vectors
  have hvec52 : (u + 2).vec = -((u + 5).vec) :=
    (by decide : ∀ a : HexDir, (a + 2).vec = -((a + 5).vec)) u
  have hvec3 : (u + 3).vec = -(u.vec) := (by decide : ∀ a : HexDir, (a + 3).vec = -(a.vec)) u
  have hvec53 : (u + 5).vec + (u + 3).vec = (u + 4).vec :=
    (by decide : ∀ a : HexDir, (a + 5).vec + (a + 3).vec = (a + 4).vec) u
  have hHeq : H = walk A u (-((i : ℤ) - 1)) := by rw [hH, head, hdA, hi]
  -- geometry
  have hG1 : nbr H (u + 2) = p := by
    rw [hHeq, hp, hA]
    simp only [walk, nbr, hvec52]
    abel
  have hG2 : nbr p (u + 3) = p2 := by
    rw [hp, hp2]
    simp only [walk, nbr, hvec3]
    module
  have hG3 : nbr p (u + 4) = R := by
    rw [hp, hR, hHeq, hA]
    simp only [walk, nbr, ← hvec53]
    abel
  have hG4 : nbr p2 (u + 5) = R := by
    rw [hp2, hR, hHeq, hA]
    simp only [walk, nbr, hvec3]
    module
  -- the two cells of the stick of `x`
  have hwalkp := T.dir_walk_backward t (i - 1) (by omega)
  have hwalkp2 := T.dir_walk_backward t i (by omega)
  rw [hdt, show (((i - 1 : ℕ) : ℤ)) = (i : ℤ) - 1 by omega] at hwalkp
  rw [hdt] at hwalkp2
  have hdp : T.dir p = u := by rw [hp]; exact hwalkp.1
  have hip : T.idx p = n - (i - 1) := by rw [hp, hwalkp.2, hit]
  have hdp2 : T.dir p2 = u := by rw [hp2]; exact hwalkp2.1
  have hip2 : T.idx p2 = n - i := by rw [hp2, hwalkp2.2, hit]
  have hile : i ≤ n := T.idx_le A
  -- the three labels presented to `R`
  have hy1 : T.label H (u + 3) = some .y1 := by
    rw [T.label_shift3 (u := u) (k := 0) (j := 3) (by rw [hdH, add_zero])
      (by decide : (3 : HexDir) = 0 + 3), if_pos hiH]
  have hb : T.label p (u + 4) = some (.b (n - i)) := by
    rw [T.label_shift4 (u := u) (k := 0) (j := 4) (by rw [hdp, add_zero])
      (by decide : (4 : HexDir) = 0 + 4), if_neg (by omega), hip,
      show n - (i - 1) - 1 = n - i from by omega]
  have ha : T.label p2 (u + 5) = some (.a (n - i)) := by
    rw [T.label_shift5 (u := u) (k := 0) (j := 5) (by rw [hdp2, add_zero])
      (by decide : (5 : HexDir) = 0 + 5), if_neg (by omega), hip2]
  have hfaceY : ∀ Q, T.label R (u + 0) = some Q → ¬ Forbidden n .y1 Q := fun Q hQ hf =>
    T.clash hv hy1 (by rw [opp_add_three']; exact hQ) hf
  have hnoneY : T.label R (u + 0) ≠ none := fun h =>
    T.no_none hy1 (by rw [opp_add_three']; exact h)
  have hfaceB : ∀ Q, T.label R (u + 1) = some Q → ¬ Forbidden n (.b (n - i)) Q := fun Q hQ hf =>
    T.clash hv hb (by rw [hG3, opp_add_four]; exact hQ) hf
  have hnoneB : T.label R (u + 1) ≠ none := fun h =>
    T.no_none hb (by rw [hG3, opp_add_four]; exact h)
  have hfaceA : ∀ Q, T.label R (u + 2) = some Q → ¬ Forbidden n (.a (n - i)) Q := fun Q hQ hf =>
    T.clash hv ha (by rw [hG4, opp_add_five]; exact hQ) hf
  have hnoneA : T.label R (u + 2) ≠ none := fun h =>
    T.no_none ha (by rw [hG4, opp_add_five]; exact h)
  have hposR := T.idx_pos R
  have hleR := T.idx_le R
  rcases hexDir_cases u (T.dir R) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir R = u + 0 := by rw [hk, add_zero]
    by_cases hj : T.idx R = n
    · exact hfaceY .y2 (by rw [T.label_shift0 hd0 (by decide : (0 : HexDir) = 0), if_pos hj])
        (forbidden_of_isY_isY (Or.inl rfl) (Or.inr rfl))
    · exact hnoneY (by rw [T.label_shift0 hd0 (by decide : (0 : HexDir) = 0), if_neg hj])
  · exfalso
    by_cases hj : T.idx R = n
    · exact hfaceY .x2 (by rw [T.label_shift5 hk (by decide : (0 : HexDir) = 1 + 5), if_pos hj])
        (Or.inl (ForbiddenCore.rule3 (Or.inl rfl) (Or.inr rfl)))
    · exact hnoneB (by rw [T.label_shift0 hk (by decide : (1 : HexDir) = 1), if_neg hj])
  · refine ⟨hk, ?_⟩
    by_contra hj
    exact hnoneA (by rw [T.label_shift0 hk (by decide : (2 : HexDir) = 2), if_neg hj])
  · exfalso
    by_cases hj : T.idx R = 1
    · exact hfaceY .y1 (by rw [T.label_shift3 hk (by decide : (0 : HexDir) = 3 + 3), if_pos hj])
        (forbidden_of_isY_isY (Or.inl rfl) (Or.inl rfl))
    · exact hnoneY (by rw [T.label_shift3 hk (by decide : (0 : HexDir) = 3 + 3), if_neg hj])
  · exfalso
    by_cases hj : T.idx R = 1
    · exact hfaceY .x1 (by rw [T.label_shift2 hk (by decide : (0 : HexDir) = 4 + 2), if_pos hj])
        (Or.inl (ForbiddenCore.rule3 (Or.inl rfl) (Or.inl rfl)))
    · exact hnoneB (by rw [T.label_shift3 hk (by decide : (1 : HexDir) = 4 + 3), if_neg hj])
  · exfalso
    by_cases hj : T.idx R = n
    · exact hfaceY .z2 (by rw [T.label_shift1 hk (by decide : (0 : HexDir) = 5 + 1), if_pos hj])
        (Or.inl (ForbiddenCore.rule10 (Or.inl rfl)))
    · by_cases hj1 : T.idx R = 1
      · refine hfaceY (.d (n - 1)) ?_ (Or.inl (ForbiddenCore.rule11 (Or.inl rfl)))
        rw [T.label_shift1 hk (by decide : (0 : HexDir) = 5 + 1), if_neg hj, hj1]
      · exact hnoneA (by rw [T.label_shift3 hk (by decide : (2 : HexDir) = 5 + 3), if_neg hj1])

/-! ### The new horizontal stick is part of a left-leaning stack -/

/-- **Every left-leaning stack has a left-leaning stack diagonally beyond its far ends.**  Let
`x` be a stick of a left-leaning stack of direction `u`.  The cell diagonally beyond the far end
of `x`, on its back side, either belongs to the same stack, or it belongs to a *new* left-leaning
stack of horizontal sticks. -/
theorem isLeftLeaningStack_backCorner (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x) :
    T.SameStack c (nbr (T.tail x) (u + 5)) ∨
      T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)) := by
  have h0n : 0 < n := by omega
  obtain ⟨hdA, hcase⟩ := T.dir_backCorner_beyond_tail hv (by omega) hL hu hx
  rcases hcase with ⟨_, hsame⟩ | ⟨hi1, hin⟩
  · exact Or.inl hsame
  refine Or.inr ?_
  set A := nbr (T.tail x) (u + 5) with hA
  set H := T.head A with hH
  have hdH : T.dir H = u := by rw [hH, T.dir_head A, hdA]
  have hiH : T.idx H = 1 := T.idx_head A
  obtain ⟨hdR, hiR⟩ := T.dir_eastCell_head_of_backCorner hv hn hL hu hx hdA hi1 hin
  set R := nbr H (u + 3) with hR
  set w := nbr H (u + 5) with hw
  set q := nbr R (u + 5) with hq
  -- the cell above the head, and the cell of the left-slanting stick above `R`
  have hdq : T.dir q = u + 2 := by
    have h1 : nbr R (T.dir R).opp = q := by rw [hdR, opp_add_two, hq]
    have := T.pred_dir R (by omega)
    rw [h1, hdR] at this
    exact this
  have hiq : T.idx q = n - 1 := by
    have h1 : nbr R (T.dir R).opp = q := by rw [hdR, opp_add_two, hq]
    have := T.pred_idx R (by omega)
    rw [h1, hiR] at this
    exact this
  have hqq : nbr q (u + 5) = nbr w (u + 4) := by
    rw [hq, hR, hw]
    simp only [nbr]
    have : (u + 3).vec + (u + 5).vec + (u + 5).vec = (u + 5).vec + (u + 4).vec :=
      (by decide : ∀ a : HexDir, (a + 3).vec + (a + 5).vec + (a + 5).vec
        = (a + 5).vec + (a + 4).vec) u
    rw [add_assoc, add_assoc]
    rw [show (u + 3).vec + ((u + 5).vec + (u + 5).vec) = (u + 3).vec + (u + 5).vec + (u + 5).vec
      from by abel, this]
    abel
  have hdqq : T.dir (nbr w (u + 4)) = u + 2 := by
    have h1 : nbr q (T.dir q).opp = nbr q (u + 5) := by rw [hdq, opp_add_two]
    have := T.pred_dir q (by omega)
    rw [h1, hdq, hqq] at this
    exact this
  have hqw : nbr w (u + 3) = q := by
    rw [hq, hR, hw]
    simp only [nbr]
    have : (u + 5).vec + (u + 3).vec = (u + 3).vec + (u + 5).vec := by abel
    rw [add_assoc, add_assoc, this]
  -- the cell above the head is the head of a horizontal stick
  have hbc := T.backCorner_head hv (by omega) (p := H) hiH
  rw [hdH] at hbc
  have hdw : T.dir w = u := by
    rcases hbc with h | h
    · rw [← hw] at h; exact h
    · exfalso
      rcases h with ⟨hd, hj⟩ | ⟨hd, hj⟩
      · rw [← hw] at hd hj
        have h1 : nbr w (T.dir w).opp = nbr w (u + 4) := by rw [hd, opp_add_one]
        have := T.pred_dir w (by omega)
        rw [h1, hd, hdqq] at this
        exact (by decide : ∀ a : HexDir, a + 2 ≠ a + 1) u this
      · rw [← hw] at hd hj
        rw [opp_add_one] at hd
        have h1 : nbr w (T.dir w) = nbr w (u + 4) := by rw [hd]
        have := T.succ_dir w (by omega)
        rw [h1, hd, hdqq] at this
        exact (by decide : ∀ a : HexDir, a + 2 ≠ a + 4) u this
  have hiw : T.idx w = 1 := by
    by_contra hjw
    have h1 : 1 < T.idx w := by have := T.idx_pos w; omega
    have h2 : nbr w (T.dir w).opp = q := by rw [hdw, opp_eq_add_three, hqw]
    have := T.pred_dir w h1
    rw [h2, hdw, hdq] at this
    exact (by decide : ∀ a : HexDir, a + 2 ≠ a) u this
  -- the two horizontal sticks ending side by side form a left-leaning pair
  have hwH : nbr w (u + 2) = H := by
    rw [hw]
    exact nbr_nbr_cancel H (opp_add_five u).symm
  have hEw : T.EndsAt w (u + 2 + 1) := by
    refine Or.inr ⟨?_, hiw⟩
    rw [hdw, show u + 2 + 1 = u + 3 from (by decide : ∀ a : HexDir, a + 2 + 1 = a + 3) u,
      opp_add_three]
  have hEH : T.EndsAt (nbr w (u + 2)) (u + 2 + 1) := by
    rw [hwH]
    refine Or.inr ⟨?_, hiH⟩
    rw [hdH, show u + 2 + 1 = u + 3 from (by decide : ∀ a : HexDir, a + 2 + 1 = a + 3) u,
      opp_add_three]
  have hpair : T.LeansLeft w (nbr w (u + 2)) := T.leansLeft_of_endsAt_pair hEw hEH
  rw [hwH] at hpair
  refine ⟨H, w, ?_, T.leansLeft_symm hpair⟩
  exact T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.head_mem_stickOf A)).symm

/-! ### A genuinely new stack above the far ends -/

/-- **Some stick of a left-leaning stack has the space `A` beyond its far end outside the
stack.**  Taking for `x` the stick of the stack whose far end sits at the very end of the stick
flanking the stack, the cell diagonally beyond the far end of `x` cannot belong to the stack
itself. -/
theorem exists_backCorner_not_sameStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ x, T.SameStack c x ∧ ¬ T.SameStack c (nbr (T.tail x) (u + 5)) := by
  have h0n : 0 < n := by omega
  -- the stick flanking the far ends of the stack, and its own far end `y`
  have hdF : T.dir (nbr (T.tail c) u) = u + 5 := by
    have := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl c)).1
    rwa [hu] at this
  have hyF : T.tail (nbr (T.tail c) u) ∈ T.stickOf (nbr (T.tail c) u) :=
    T.tail_mem_stickOf h0n _
  have hdy : T.dir (T.tail (nbr (T.tail c) u)) = u + 5 := by rw [T.dir_tail h0n, hdF]
  have hiy : T.idx (T.tail (nbr (T.tail c) u)) = n := T.idx_tail h0n _
  obtain ⟨x, hx, hxy⟩ := T.exists_sameStack_of_mem_flankingStick hv hn hL
    (y := T.tail (nbr (T.tail c) u)) (by rw [hu]; exact hyF)
  rw [hu] at hxy
  refine ⟨x, hx, fun hsame => ?_⟩
  have hdA : T.dir (nbr (T.tail x) (u + 5)) = u :=
    (T.dir_backCorner_beyond_tail hv hn hL hu hx).1
  -- the cell beyond the far end of the new stick lies on the flanking stick
  have hmem : T.frontCell u (nbr (T.tail x) (u + 5)) ∈ T.stickOf (T.frontCell u c) :=
    (T.frontCell_mem_of_sameStack hv h0n (d := u) (by rw [hu]; exact sameAxis_self u) hsame).2
  rw [show T.frontCell u c = nbr (T.tail c) u from by rw [frontCell, endCell, if_pos hu],
    show T.frontCell u (nbr (T.tail x) (u + 5))
        = nbr (T.tail (nbr (T.tail x) (u + 5))) u from by rw [frontCell, endCell, if_pos hdA]]
    at hmem
  -- both that cell and `y` lie on the flanking stick, so they differ by a multiple of `u + 5`
  obtain ⟨k, hk⟩ := T.exists_walk_of_mem_stickOf hmem hyF
  rw [hdF] at hk
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (n : ℤ) - T.idx (nbr (T.tail x) (u + 5)) = m := ⟨_, rfl⟩
  have htailA : T.tail (nbr (T.tail x) (u + 5))
      = walk (nbr (T.tail x) (u + 5)) u m := by rw [T.tail_eq_walk h0n, hdA, hm]
  have hk2 := hk
  rw [htailA, ← hxy] at hk2
  have hkey : m • u.vec = (k - 1) • (u + 5).vec := by
    simp only [walk, nbr] at hk2
    linear_combination (norm := module) hk2
  obtain ⟨-, hk1⟩ := smul_vec_eq_smul_vec
    ((by decide : ∀ a : HexDir, a ≠ a + 5) u)
    (by rw [opp_add_five]; exact (by decide : ∀ a : HexDir, a ≠ a + 2) u) hkey
  -- so that cell is one step beyond the far end of the flanking stick, which is impossible
  rw [show k = 1 from by omega, ← nbr_eq_walk_one] at hk
  rw [hk, ← T.stickOf_eq_of_mem hyF] at hmem
  exact T.nbr_dir_not_mem_stickOf hiy (by rw [hdy]; exact hmem)

/-- **Every left-leaning stack has a left-leaning stack above it.**  A left-leaning stack of
horizontal sticks of direction `u` has, diagonally beyond its far ends, a *different*
left-leaning stack of horizontal sticks, again of direction `u`.  This is the conclusion of
Figures 13 to 15 of the paper. -/
theorem exists_stackAbove_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ c', T.dir c' = u ∧ T.IsLeftLeaningStack c' ∧ T.StackAbove u c c' := by
  have h0n : 0 < n := by omega
  obtain ⟨x, hx, hne⟩ := T.exists_backCorner_not_sameStack hv (by omega) hL hu
  have hdA : T.dir (nbr (T.tail x) (u + 5)) = u :=
    (T.dir_backCorner_beyond_tail hv (by omega) hL hu hx).1
  have hLA : T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)) := by
    rcases T.isLeftLeaningStack_backCorner hv hn hL hu hx with h | h
    · exact absurd h hne
    · exact h
  refine ⟨nbr (T.tail x) (u + 5), hdA, hLA, hne, T.tail x, ?_, Or.inr (T.sameStack_refl _)⟩
  exact SameStack.trans T hx
    (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n x)).symm)

end StickTiling

end StickPolyhex
