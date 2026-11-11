import Tiling.Proofs.Stacks

/-!
# Corner cells of a stick, and what may cover them

This file contains the local analysis, in terms of the matching rules, of the two cells that
sit next to a cell `p` of a stick on the two sides of the stick:

* the *front corner* `nbr p (dir p + 1)`, the concave corner between `p` and the next cell of
  the stick on the `dir p + 1` side, and
* the *back corner* `nbr p (dir p + 5)`, the concave corner on the other side.

The main results are:

* `not_sameAxis_dir_frontCorner` (**Theorem P**): the front corner of a cell of a stick is never
  covered by a stick whose axis is `dir p + 1`;
* `endsAt_backCorner_of_sameAxis`: if the back corner is covered by a stick of axis `dir p + 1`,
  then that stick *ends* at the corner;
* the propagation lemmas `corner_step_forward_A`, `corner_step_forward_B` and
  `corner_step_backward_A`, saying that a stick ending at one back corner of a stick forces
  sticks ending at the neighbouring back corners in the same way;
* `backCorner_head`: the back corner at the head of a stick is covered either by a parallel
  stick or by a stick ending there;
* `corner_beyond_tail`: a back corner lying just beyond the tail of a parallel stick is covered
  by the head of a stick pointing in the direction `dir p + 5`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Arithmetic of directions -/

lemma opp_add_one (a : HexDir) : (a + 1).opp = a + 4 := by revert a; decide
lemma opp_add_two (a : HexDir) : (a + 2).opp = a + 5 := by revert a; decide
lemma opp_add_three (a : HexDir) : (a + 3).opp = a := by revert a; decide
lemma opp_add_four (a : HexDir) : (a + 4).opp = a + 1 := by revert a; decide
lemma opp_add_five (a : HexDir) : (a + 5).opp = a + 2 := by revert a; decide
lemma opp_add_three' (a : HexDir) : (a + 3).opp = a + 0 := by revert a; decide
lemma opp_add_zero' (a : HexDir) : (a + 0).opp = a + 3 := by revert a; decide

lemma vec_zero_four (a : HexDir) : a.vec + (a + 4).vec = (a + 5).vec := by revert a; decide
lemma vec_four_zero (a : HexDir) : (a + 4).vec + a.vec = (a + 5).vec := by revert a; decide
lemma vec_four_zero' (a : HexDir) : (a + 4).vec + (a + 0).vec = (a + 5).vec := by revert a; decide
lemma vec_five_three' (a : HexDir) : (a + 5).vec + (a + 3).vec = (a + 4).vec := by revert a; decide
lemma vec_zero_two (a : HexDir) : a.vec + (a + 2).vec = (a + 1).vec := by revert a; decide
lemma vec_five_three (a : HexDir) : (a + 5).vec + (a + 3).vec = (a + 4).vec := by revert a; decide
lemma vec_four_two (a : HexDir) : (a + 4).vec + (a + 2).vec = (a + 3).vec := by revert a; decide
lemma vec_one_three (a : HexDir) : (a + 1).vec + (a + 3).vec = (a + 2).vec := by revert a; decide
lemma vec_three_one (a : HexDir) : (a + 3).vec + (a + 1).vec = (a + 2).vec := by revert a; decide
lemma vec_three_five (a : HexDir) : (a + 3).vec + (a + 5).vec = (a + 4).vec := by revert a; decide
lemma add_one_one (a : HexDir) : a + 1 + 1 = a + 2 := by revert a; decide
lemma vec_add_three (a : HexDir) : (a + 3).vec = -a.vec := by revert a; decide

/-! ### A convenient form of the label computation -/

/-- The label of the edge of `c` in a direction given as `T.dir c + k`. -/
lemma label_of_eq {c : Hex} {v : HexDir} (k : HexDir) (h : v = T.dir c + k) :
    T.label c v = frameLabel n (T.idx c) (k + HexDir.W) := by
  rw [h]; exact T.label_dir_add c k

/-- The label presented by a neighbouring cell, together with the fact that the two labels are
not forbidden from meeting. -/
lemma label_nbr_of_label (hv : T.SatisfiesWeaveRules) {c : Hex} {e : HexDir} {p : StickEdge}
    (h : T.label c e = some p) :
    ∃ q, T.label (nbr c e) e.opp = some q ∧ ¬ Forbidden n p q := by
  have hne : T.label (nbr c e) e.opp ≠ none := by
    intro hnone
    rw [← T.label_eq_none_comm c e] at hnone
    rw [hnone] at h
    exact Option.some_ne_none p h.symm
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hne
  exact ⟨q, hq, fun hf => hv c e p q h hq hf⟩

/-- The label of `c` in the direction `u + j`, when `T.dir c = u + k` and `j = k`. -/
lemma label_shift0 {c : Hex} {u k j : HexDir} (hd : T.dir c = u + k) (h : j = k) :
    T.label c (u + j) = if T.idx c = n then some .y2 else none := by
  rw [show u + j = T.dir c by rw [hd, h]]
  exact T.label_dir c

/-- The label of `c` in the direction `u + j`, when `T.dir c = u + k` and `j = k + 1`. -/
lemma label_shift1 {c : Hex} {u k j : HexDir} (hd : T.dir c = u + k) (h : j = k + 1) :
    T.label c (u + j) = if T.idx c = n then some .z2 else some (.d (n - T.idx c)) := by
  rw [show u + j = T.dir c + 1 by rw [hd, h]; ring]
  exact T.label_dir_add_one c

/-- The label of `c` in the direction `u + j`, when `T.dir c = u + k` and `j = k + 2`. -/
lemma label_shift2 {c : Hex} {u k j : HexDir} (hd : T.dir c = u + k) (h : j = k + 2) :
    T.label c (u + j) = if T.idx c = 1 then some .x1 else some (.c (n + 1 - T.idx c)) := by
  rw [show u + j = T.dir c + 2 by rw [hd, h]; ring]
  exact T.label_dir_add_two c

/-- The label of `c` in the direction `u + j`, when `T.dir c = u + k` and `j = k + 3`. -/
lemma label_shift3 {c : Hex} {u k j : HexDir} (hd : T.dir c = u + k) (h : j = k + 3) :
    T.label c (u + j) = if T.idx c = 1 then some .y1 else none := by
  rw [show u + j = (T.dir c).opp by rw [hd, h, opp_eq_add_three]; ring]
  exact T.label_opp_dir c

/-- The label of `c` in the direction `u + j`, when `T.dir c = u + k` and `j = k + 4`. -/
lemma label_shift4 {c : Hex} {u k j : HexDir} (hd : T.dir c = u + k) (h : j = k + 4) :
    T.label c (u + j) = if T.idx c = 1 then some .z1 else some (.b (T.idx c - 1)) := by
  rw [show u + j = T.dir c + 4 by rw [hd, h]; ring]
  exact T.label_dir_add_four c

/-- The label of `c` in the direction `u + j`, when `T.dir c = u + k` and `j = k + 5`. -/
lemma label_shift5 {c : Hex} {u k j : HexDir} (hd : T.dir c = u + k) (h : j = k + 5) :
    T.label c (u + j) = if T.idx c = n then some .x2 else some (.a (T.idx c)) := by
  rw [show u + j = T.dir c + 5 by rw [hd, h]; ring]
  exact T.label_dir_add_five c

/-- Two labels that face each other may not be forbidden. -/
lemma clash (hv : T.SatisfiesWeaveRules) {c : Hex} {e : HexDir} {P Q : StickEdge}
    (h1 : T.label c e = some P) (h2 : T.label (nbr c e) e.opp = some Q)
    (hf : Forbidden n P Q) : False := hv c e P Q h1 h2 hf

/-- An edge carrying a label on one side carries one on the other side too. -/
lemma no_none {c : Hex} {e : HexDir} {P : StickEdge} (h1 : T.label c e = some P)
    (h2 : T.label (nbr c e) e.opp = none) : False := by
  rw [← T.label_eq_none_comm c e] at h2
  rw [h2] at h1
  exact Option.some_ne_none P h1.symm

/-! ### Theorem P: the front corner is never covered by a stick of the perpendicular axis -/

/-- If the front corner of a cell of a stick is covered by a stick with axis `dir p + 1`, then
that stick ends at the corner, in the direction `dir p + 4`. -/
lemma endsAt_frontCorner_of_sameAxis {p : Hex}
    (hax : SameAxis (T.dir p + 1) (T.dir (nbr p (T.dir p + 1)))) :
    T.EndsAt (nbr p (T.dir p + 1)) (T.dir p + 4) := by
  obtain ⟨P, hP⟩ : ∃ P, T.label p (T.dir p + 1) = some P := by
    rw [T.label_dir_add_one]; split <;> exact ⟨_, rfl⟩
  have hne : T.label (nbr p (T.dir p + 1)) (T.dir p + 4) ≠ none := fun h =>
    T.no_none hP (by rw [opp_add_one]; exact h)
  rcases hax with hd | hd
  · right
    refine ⟨by rw [hd, opp_add_four], ?_⟩
    by_contra hi
    exact hne (by
      rw [T.label_shift3 hd (by decide : (4 : HexDir) = 1 + 3), if_neg hi])
  · rw [opp_add_one] at hd
    left
    refine ⟨hd, ?_⟩
    by_contra hi
    exact hne (by
      rw [T.label_shift0 hd (by decide : (4 : HexDir) = 4), if_neg hi])

/-- The base case of Theorem P: the front corner of the *head* of a stick is not covered by a
stick of axis `dir p + 1` (rule 11). -/
lemma not_sameAxis_dir_frontCorner_head (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p : Hex}
    (hp : T.idx p = 1) :
    ¬ SameAxis (T.dir p + 1) (T.dir (nbr p (T.dir p + 1))) := by
  intro hax
  obtain ⟨q, hq, hqy⟩ := (T.endsAt_frontCorner_of_sameAxis hax).label_isY
  have hlp : T.label p (T.dir p + 1) = some (.d (n - 1)) := by
    rw [T.label_dir_add_one, if_neg (by omega), hp]
  exact T.clash hv hlp (by rw [opp_add_one]; exact hq) (Or.inr (ForbiddenCore.rule11 hqy))

/-- The descent step of Theorem P: if the front corner of `p` is covered by a stick of axis
`dir p + 1`, then so is the front corner of the previous cell of the stick of `p`. -/
lemma sameAxis_frontCorner_pred (hv : T.SatisfiesWeaveRules) {p : Hex} (h2 : 2 ≤ T.idx p)
    (hax : SameAxis (T.dir p + 1) (T.dir (nbr p (T.dir p + 1)))) :
    SameAxis (T.dir (nbr p (T.dir p).opp) + 1)
      (T.dir (nbr (nbr p (T.dir p).opp) (T.dir (nbr p (T.dir p).opp) + 1))) := by
  have hle := T.idx_le p
  have hdp' : T.dir (nbr p (T.dir p).opp) = T.dir p := T.pred_dir p (by omega)
  rw [hdp']
  have hx' : nbr (nbr p (T.dir p).opp) (T.dir p + 1) = nbr p (T.dir p + 2) := by
    rw [opp_eq_add_three]; exact nbr_nbr_of_vec p (vec_three_one (T.dir p))
  rw [hx']
  set x' := nbr p (T.dir p + 2) with hx'def
  have hxx' : nbr (nbr p (T.dir p + 1)) (T.dir p + 3) = x' :=
    nbr_nbr_of_vec p (vec_one_three (T.dir p))
  obtain ⟨X, hX, hXx⟩ : ∃ X, T.label (nbr p (T.dir p + 1)) (T.dir p + 3) = some X ∧ IsX X := by
    rcases T.endsAt_frontCorner_of_sameAxis hax with ⟨hd, hi⟩ | ⟨hd, hi⟩
    · exact ⟨.x2, by rw [T.label_shift5 hd (by decide : (3 : HexDir) = 4 + 5), if_pos hi],
        Or.inr rfl⟩
    · rw [opp_add_four] at hd
      exact ⟨.x1, by rw [T.label_shift2 hd (by decide : (3 : HexDir) = 1 + 2), if_pos hi],
        Or.inl rfl⟩
  have hc : T.label p (T.dir p + 2) = some (.c (n + 1 - T.idx p)) := by
    rw [T.label_dir_add_two, if_neg (by omega)]
  have hXface : ∀ Q, T.label x' (T.dir p + 0) = some Q → ¬ Forbidden n X Q := by
    intro Q hQ hf
    exact T.clash hv hX (by rw [hxx', opp_add_three']; exact hQ) hf
  have hXnone : T.label x' (T.dir p + 0) ≠ none := fun h =>
    T.no_none hX (by rw [hxx', opp_add_three']; exact h)
  have hcnone : T.label x' (T.dir p + 5) ≠ none := fun h =>
    T.no_none hc (by rw [opp_add_two]; exact h)
  have hpos := T.idx_pos x'
  have hle' := T.idx_le x'
  rcases hexDir_cases (T.dir p) (T.dir x') with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir x' = T.dir p + 0 := by rw [hk, add_zero]
    rw [T.label_shift0 hd0 (by decide : (0 : HexDir) = 0)] at hXface hXnone
    by_cases hi : T.idx x' = n
    · exact hXface .y2 (by rw [if_pos hi]) (forbidden_of_isX_isY hXx (Or.inr rfl))
    · exact hXnone (by rw [if_neg hi])
  · exact Or.inl hk
  · exfalso
    rw [T.label_shift4 hk (by decide : (0 : HexDir) = 2 + 4)] at hXface hXnone
    rw [T.label_shift3 hk (by decide : (5 : HexDir) = 2 + 3)] at hcnone
    by_cases hi : T.idx x' = 1
    · exact hXface .z1 (by rw [if_pos hi]) (forbidden_of_isX_isZ hXx (Or.inl rfl))
    · exact hcnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift3 hk (by decide : (0 : HexDir) = 3 + 3)] at hXface hXnone
    by_cases hi : T.idx x' = 1
    · exact hXface .y1 (by rw [if_pos hi]) (forbidden_of_isX_isY hXx (Or.inl rfl))
    · exact hXnone (by rw [if_neg hi])
  · exact Or.inr (by rw [hk, opp_add_one])
  · exfalso
    rw [T.label_shift1 hk (by decide : (0 : HexDir) = 5 + 1)] at hXface hXnone
    rw [T.label_shift0 hk (by decide : (5 : HexDir) = 5)] at hcnone
    by_cases hi : T.idx x' = n
    · exact hXface .z2 (by rw [if_pos hi]) (forbidden_of_isX_isZ hXx (Or.inr rfl))
    · exact hcnone (by rw [if_neg hi])

/-- **Theorem P.**  In a valid tiling the concave corner in front of a cell `p` of a stick (the
corner on the `dir p + 1` side) is never covered by a stick whose axis is `dir p + 1`. -/
theorem not_sameAxis_dir_frontCorner (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p : Hex} (hp : T.idx p < n) :
    ¬ SameAxis (T.dir p + 1) (T.dir (nbr p (T.dir p + 1))) := by
  suffices h : ∀ j : ℕ, ∀ p : Hex, T.idx p ≤ j → T.idx p < n →
      ¬ SameAxis (T.dir p + 1) (T.dir (nbr p (T.dir p + 1))) from h (T.idx p) p le_rfl hp
  intro j
  induction j with
  | zero => intro p hj _; exact absurd hj (by have := T.idx_pos p; omega)
  | succ j ih =>
    intro p hj hpn hax
    rcases eq_or_lt_of_le (T.idx_pos p) with h1 | h1
    · exact T.not_sameAxis_dir_frontCorner_head hv hn h1.symm hax
    · have h2 : 2 ≤ T.idx p := h1
      have hpred := T.sameAxis_frontCorner_pred hv h2 hax
      have hd : T.dir (nbr p (T.dir p).opp) = T.dir p := T.pred_dir p h1
      have hi : T.idx (nbr p (T.dir p).opp) = T.idx p - 1 := T.pred_idx p h1
      exact ih _ (by omega) (by omega) hpred

/-! ### Back corners -/

/-- If the back corner of a cell `p` of a stick (with `p` not the last cell) is covered by a
stick with axis `dir p + 1`, then that stick ends at the corner. -/
lemma endsAt_backCorner_of_sameAxis {p : Hex} (hp : T.idx p < n)
    (hax : SameAxis (T.dir p + 1) (T.dir (nbr p (T.dir p + 5)))) :
    T.EndsAt (nbr p (T.dir p + 5)) (T.dir p + 1) := by
  have hnbr : nbr (nbr p (T.dir p)) (T.dir p + 4) = nbr p (T.dir p + 5) :=
    nbr_nbr_of_vec p (vec_zero_four (T.dir p))
  have hd2 : T.dir (nbr p (T.dir p)) = T.dir p := T.succ_dir p hp
  have hi2 : T.idx (nbr p (T.dir p)) = T.idx p + 1 := T.succ_idx p hp
  have hpos := T.idx_pos p
  obtain ⟨P, hP⟩ : ∃ P, T.label (nbr p (T.dir p)) (T.dir p + 4) = some P := by
    rw [T.label_shift4 (u := T.dir p) (k := 0) (j := 4) (by rw [hd2, add_zero])
      (by decide : (4 : HexDir) = 0 + 4)]
    split <;> exact ⟨_, rfl⟩
  have hne : T.label (nbr p (T.dir p + 5)) (T.dir p + 1) ≠ none := by
    intro h
    refine T.no_none hP ?_
    rw [hnbr, opp_add_four]
    exact h
  rcases hax with hd | hd
  · left
    refine ⟨hd, ?_⟩
    by_contra hi
    exact hne (by rw [T.label_shift0 hd (by decide : (1 : HexDir) = 1), if_neg hi])
  · rw [opp_add_one] at hd
    right
    refine ⟨by rw [hd, opp_add_one], ?_⟩
    by_contra hi
    exact hne (by rw [T.label_shift3 hd (by decide : (1 : HexDir) = 4 + 3), if_neg hi])

/-- Propagation along the back corners of a stick, case A (the covering sticks have direction
`dir p + 1` and end at the corners with their last cell): from the corner behind `p` to the
corner in front of it. -/
lemma corner_step_forward_A (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p : Hex} (hp : T.idx p < n)
    (h1 : T.dir (nbr p (T.dir p + 4)) = T.dir p + 1) (h2 : T.idx (nbr p (T.dir p + 4)) = n) :
    T.dir (nbr p (T.dir p + 5)) = T.dir p + 1 ∧ T.idx (nbr p (T.dir p + 5)) = n := by
  have hpos := T.idx_pos p
  set z := nbr p (T.dir p + 5) with hz
  have hyz : nbr (nbr p (T.dir p + 4)) (T.dir p + 0) = z := nbr_nbr_of_vec p (vec_four_zero' _)
  have hpz : nbr (nbr p (T.dir p)) (T.dir p + 4) = z := nbr_nbr_of_vec p (vec_zero_four _)
  have hd2 : T.dir (nbr p (T.dir p)) = T.dir p := T.succ_dir p hp
  have hi2 : T.idx (nbr p (T.dir p)) = T.idx p + 1 := T.succ_idx p hp
  have hX : T.label (nbr p (T.dir p + 4)) (T.dir p + 0) = some .x2 := by
    rw [T.label_shift5 h1 (by decide : (0 : HexDir) = 1 + 5), if_pos h2]
  have hXface : ∀ Q, T.label z (T.dir p + 3) = some Q → ¬ Forbidden n .x2 Q := fun Q hQ hf =>
    T.clash hv hX (by rw [hyz, opp_add_zero']; exact hQ) hf
  have hXnone : T.label z (T.dir p + 3) ≠ none := fun h =>
    T.no_none hX (by rw [hyz, opp_add_zero']; exact h)
  have hb : T.label (nbr p (T.dir p)) (T.dir p + 4) = some (.b (T.idx p)) := by
    rw [T.label_shift4 (u := T.dir p) (k := 0) (by rw [hd2, add_zero])
      (by decide : (4 : HexDir) = 0 + 4), if_neg (by omega), hi2]
    simp
  have hbnone : T.label z (T.dir p + 1) ≠ none := fun h =>
    T.no_none hb (by rw [hpz, opp_add_four]; exact h)
  have ha : T.label p (T.dir p + 5) = some (.a (T.idx p)) := by
    rw [T.label_dir_add_five, if_neg (by omega)]
  have hanone : T.label z (T.dir p + 2) ≠ none := fun h =>
    T.no_none ha (by rw [opp_add_five]; exact h)
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  rcases hexDir_cases (T.dir p) (T.dir z) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir z = T.dir p + 0 := by rw [hk, add_zero]
    rw [T.label_shift3 hd0 (by decide : (3 : HexDir) = 0 + 3)] at hXface hXnone
    by_cases hi : T.idx z = 1
    · exact hXface .y1 (by rw [if_pos hi]) (forbidden_of_isX_isY (Or.inr rfl) (Or.inl rfl))
    · exact hXnone (by rw [if_neg hi])
  · rw [T.label_shift2 hk (by decide : (3 : HexDir) = 1 + 2)] at hXface hXnone
    rw [T.label_shift0 hk (by decide : (1 : HexDir) = 1)] at hbnone
    refine ⟨hk, ?_⟩
    by_contra hi
    exact hbnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift1 hk (by decide : (3 : HexDir) = 2 + 1)] at hXface hXnone
    rw [T.label_shift0 hk (by decide : (2 : HexDir) = 2)] at hanone
    by_cases hi : T.idx z = n
    · exact hXface .z2 (by rw [if_pos hi]) (forbidden_of_isX_isZ (Or.inr rfl) (Or.inr rfl))
    · exact hanone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift0 hk (by decide : (3 : HexDir) = 3)] at hXface hXnone
    by_cases hi : T.idx z = n
    · exact hXface .y2 (by rw [if_pos hi]) (forbidden_of_isX_isY (Or.inr rfl) (Or.inr rfl))
    · exact hXnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift5 hk (by decide : (3 : HexDir) = 4 + 5)] at hXface hXnone
    by_cases hi : T.idx z = n
    · exact hXface .x2 (by rw [if_pos hi])
        (Or.inl (ForbiddenCore.rule2x (Or.inr rfl) (Or.inr rfl)))
    · exact hXface (.a (T.idx z)) (by rw [if_neg hi])
        (Or.inl (ForbiddenCore.rule8 hposz (by omega)))
  · exfalso
    rw [T.label_shift4 hk (by decide : (3 : HexDir) = 5 + 4)] at hXface hXnone
    rw [T.label_shift3 hk (by decide : (2 : HexDir) = 5 + 3)] at hanone
    by_cases hi : T.idx z = 1
    · exact hXface .z1 (by rw [if_pos hi]) (forbidden_of_isX_isZ (Or.inr rfl) (Or.inl rfl))
    · exact hanone (by rw [if_neg hi])

/-- Propagation along the back corners of a stick, case B (the covering sticks have direction
`dir p + 4` and begin at the corners with their first cell). -/
lemma corner_step_forward_B (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p : Hex} (hp : T.idx p < n)
    (h1 : T.dir (nbr p (T.dir p + 4)) = T.dir p + 4) (h2 : T.idx (nbr p (T.dir p + 4)) = 1) :
    T.dir (nbr p (T.dir p + 5)) = T.dir p + 4 ∧ T.idx (nbr p (T.dir p + 5)) = 1 := by
  have hpos := T.idx_pos p
  set z := nbr p (T.dir p + 5) with hz
  have hyz : nbr (nbr p (T.dir p + 4)) (T.dir p + 0) = z := nbr_nbr_of_vec p (vec_four_zero' _)
  have hpz : nbr (nbr p (T.dir p)) (T.dir p + 4) = z := nbr_nbr_of_vec p (vec_zero_four _)
  have hd2 : T.dir (nbr p (T.dir p)) = T.dir p := T.succ_dir p hp
  have hi2 : T.idx (nbr p (T.dir p)) = T.idx p + 1 := T.succ_idx p hp
  have hX : T.label (nbr p (T.dir p + 4)) (T.dir p + 0) = some .x1 := by
    rw [T.label_shift2 h1 (by decide : (0 : HexDir) = 4 + 2), if_pos h2]
  have hXface : ∀ Q, T.label z (T.dir p + 3) = some Q → ¬ Forbidden n .x1 Q := fun Q hQ hf =>
    T.clash hv hX (by rw [hyz, opp_add_zero']; exact hQ) hf
  have hXnone : T.label z (T.dir p + 3) ≠ none := fun h =>
    T.no_none hX (by rw [hyz, opp_add_zero']; exact h)
  have hb : T.label (nbr p (T.dir p)) (T.dir p + 4) = some (.b (T.idx p)) := by
    rw [T.label_shift4 (u := T.dir p) (k := 0) (by rw [hd2, add_zero])
      (by decide : (4 : HexDir) = 0 + 4), if_neg (by omega), hi2]
    simp
  have hbnone : T.label z (T.dir p + 1) ≠ none := fun h =>
    T.no_none hb (by rw [hpz, opp_add_four]; exact h)
  have ha : T.label p (T.dir p + 5) = some (.a (T.idx p)) := by
    rw [T.label_dir_add_five, if_neg (by omega)]
  have hanone : T.label z (T.dir p + 2) ≠ none := fun h =>
    T.no_none ha (by rw [opp_add_five]; exact h)
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  rcases hexDir_cases (T.dir p) (T.dir z) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir z = T.dir p + 0 := by rw [hk, add_zero]
    rw [T.label_shift3 hd0 (by decide : (3 : HexDir) = 0 + 3)] at hXface hXnone
    by_cases hi : T.idx z = 1
    · exact hXface .y1 (by rw [if_pos hi]) (forbidden_of_isX_isY (Or.inl rfl) (Or.inl rfl))
    · exact hXnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift2 hk (by decide : (3 : HexDir) = 1 + 2)] at hXface hXnone
    by_cases hi : T.idx z = 1
    · exact hXface .x1 (by rw [if_pos hi])
        (Or.inl (ForbiddenCore.rule2x (Or.inl rfl) (Or.inl rfl)))
    · exact hXface (.c (n + 1 - T.idx z)) (by rw [if_neg hi])
        (Or.inl (ForbiddenCore.rule6 (by omega) (by omega)))
  · exfalso
    rw [T.label_shift1 hk (by decide : (3 : HexDir) = 2 + 1)] at hXface hXnone
    rw [T.label_shift0 hk (by decide : (2 : HexDir) = 2)] at hanone
    by_cases hi : T.idx z = n
    · exact hXface .z2 (by rw [if_pos hi]) (forbidden_of_isX_isZ (Or.inl rfl) (Or.inr rfl))
    · exact hanone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift0 hk (by decide : (3 : HexDir) = 3)] at hXface hXnone
    by_cases hi : T.idx z = n
    · exact hXface .y2 (by rw [if_pos hi]) (forbidden_of_isX_isY (Or.inl rfl) (Or.inr rfl))
    · exact hXnone (by rw [if_neg hi])
  · rw [T.label_shift5 hk (by decide : (3 : HexDir) = 4 + 5)] at hXface hXnone
    rw [T.label_shift3 hk (by decide : (1 : HexDir) = 4 + 3)] at hbnone
    refine ⟨hk, ?_⟩
    by_contra hi
    exact hbnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift4 hk (by decide : (3 : HexDir) = 5 + 4)] at hXface hXnone
    rw [T.label_shift3 hk (by decide : (2 : HexDir) = 5 + 3)] at hanone
    by_cases hi : T.idx z = 1
    · exact hXface .z1 (by rw [if_pos hi]) (forbidden_of_isX_isZ (Or.inl rfl) (Or.inl rfl))
    · exact hanone (by rw [if_neg hi])

/-- Propagation along the back corners of a stick, case A, in the backward direction.  This uses
Theorem P to exclude the corner being covered by a stick of axis `dir p + 2`. -/
lemma corner_step_backward_A (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p : Hex}
    (h1 : T.dir (nbr p (T.dir p + 5)) = T.dir p + 1) (h2 : T.idx (nbr p (T.dir p + 5)) = n) :
    T.dir (nbr p (T.dir p + 4)) = T.dir p + 1 ∧ T.idx (nbr p (T.dir p + 4)) = n := by
  set y := nbr p (T.dir p + 5) with hy
  set w := nbr p (T.dir p + 4) with hw
  have hyw : nbr y (T.dir p + 3) = w := nbr_nbr_of_vec p (vec_five_three _)
  -- the label `c 1` presented by `y` to `w`
  have hc : T.label y (T.dir p + 3) = some (.c 1) := by
    rw [T.label_shift2 h1 (by decide : (3 : HexDir) = 1 + 2), if_neg (by omega), h2,
      show n + 1 - n = 1 from by omega]
  have hcface : ∀ Q, T.label w (T.dir p + 0) = some Q → ¬ Forbidden n (.c 1) Q := fun Q hQ hf =>
    T.clash hv hc (by rw [hyw, opp_add_three']; exact hQ) hf
  have hcnone : T.label w (T.dir p + 0) ≠ none := fun h =>
    T.no_none hc (by rw [hyw, opp_add_three']; exact h)
  -- the label presented by `p` to `w`
  obtain ⟨P, hP⟩ : ∃ P, T.label p (T.dir p + 4) = some P := by
    rw [T.label_dir_add_four]; split <;> exact ⟨_, rfl⟩
  have hPnone : T.label w (T.dir p + 1) ≠ none := fun h =>
    T.no_none hP (by rw [opp_add_four]; exact h)
  -- Theorem P applied to the cell of the stick of `y` just before `y`
  have hyopp : (T.dir y).opp = T.dir p + 4 := by rw [h1, opp_add_one]
  have hdq : T.dir (nbr y (T.dir p + 4)) = T.dir p + 1 := by
    rw [← hyopp, T.pred_dir y (by omega), h1]
  have hiq : T.idx (nbr y (T.dir p + 4)) = n - 1 := by
    rw [← hyopp, T.pred_idx y (by omega), h2]
  have hcorner : nbr (nbr y (T.dir p + 4)) (T.dir p + 2) = w := by
    rw [nbr_nbr_of_vec y (vec_four_two (T.dir p)), hyw]
  have hPthm := T.not_sameAxis_dir_frontCorner hv hn (p := nbr y (T.dir p + 4)) (by omega)
  rw [hdq, add_one_one, hcorner] at hPthm
  have hposw := T.idx_pos w
  have hlew := T.idx_le w
  rcases hexDir_cases (T.dir p) (T.dir w) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir w = T.dir p + 0 := by rw [hk, add_zero]
    rw [T.label_shift0 hd0 (by decide : (0 : HexDir) = 0)] at hcface hcnone
    by_cases hi : T.idx w = n
    · exact hcface .y2 (by rw [if_pos hi])
        (Or.inr (ForbiddenCore.rule5 (Or.inr rfl) (Or.inr rfl)))
    · exact hcnone (by rw [if_neg hi])
  · rw [T.label_shift0 hk (by decide : (1 : HexDir) = 1)] at hPnone
    refine ⟨hk, ?_⟩
    by_contra hi
    exact hPnone (by rw [if_neg hi])
  · exact absurd (Or.inl hk) hPthm
  · exfalso
    rw [T.label_shift3 hk (by decide : (0 : HexDir) = 3 + 3)] at hcface hcnone
    by_cases hi : T.idx w = 1
    · exact hcface .y1 (by rw [if_pos hi])
        (Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inr rfl)))
    · exact hcnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift2 hk (by decide : (0 : HexDir) = 4 + 2)] at hcface hcnone
    rw [T.label_shift3 hk (by decide : (1 : HexDir) = 4 + 3)] at hPnone
    by_cases hi : T.idx w = 1
    · exact hcface .x1 (by rw [if_pos hi])
        (Or.inr (ForbiddenCore.rule6 (le_refl 1) (by omega)))
    · exact hPnone (by rw [if_neg hi])
  · exact absurd (Or.inr (by rw [hk, opp_add_two])) hPthm

/-- The cell filling the back corner at the head of a stick is covered either by a parallel
stick, or by a stick that ends at the corner. -/
lemma backCorner_head (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p : Hex} (hp : T.idx p = 1) :
    T.dir (nbr p (T.dir p + 5)) = T.dir p ∨ T.EndsAt (nbr p (T.dir p + 5)) (T.dir p + 1) := by
  have hpn : T.idx p < n := by omega
  set v := nbr p (T.dir p + 5) with hvdef
  have hpv : nbr (nbr p (T.dir p)) (T.dir p + 4) = v := nbr_nbr_of_vec p (vec_zero_four _)
  have hd2 : T.dir (nbr p (T.dir p)) = T.dir p := T.succ_dir p hpn
  have hi2 : T.idx (nbr p (T.dir p)) = T.idx p + 1 := T.succ_idx p hpn
  have ha : T.label p (T.dir p + 5) = some (.a 1) := by
    rw [T.label_dir_add_five, if_neg (by omega), hp]
  have haface : ∀ Q, T.label v (T.dir p + 2) = some Q → ¬ Forbidden n (.a 1) Q := fun Q hQ hf =>
    T.clash hv ha (by rw [opp_add_five]; exact hQ) hf
  have hanone : T.label v (T.dir p + 2) ≠ none := fun h =>
    T.no_none ha (by rw [opp_add_five]; exact h)
  have hb : T.label (nbr p (T.dir p)) (T.dir p + 4) = some (.b 1) := by
    rw [T.label_shift4 (u := T.dir p) (k := 0) (by rw [hd2, add_zero])
      (by decide : (4 : HexDir) = 0 + 4), if_neg (by omega), hi2, hp]
  have hbnone : T.label v (T.dir p + 1) ≠ none := fun h =>
    T.no_none hb (by rw [hpv, opp_add_four]; exact h)
  have hposv := T.idx_pos v
  have hlev := T.idx_le v
  rcases hexDir_cases (T.dir p) (T.dir v) with hk | hk | hk | hk | hk | hk
  · exact Or.inl hk
  · refine Or.inr (Or.inl ⟨hk, ?_⟩)
    rw [T.label_shift0 hk (by decide : (1 : HexDir) = 1)] at hbnone
    by_contra hi
    exact hbnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift0 hk (by decide : (2 : HexDir) = 2)] at haface hanone
    by_cases hi : T.idx v = n
    · exact haface .y2 (by rw [if_pos hi])
        (Or.inr (ForbiddenCore.rule5 (Or.inr rfl) (Or.inl rfl)))
    · exact hanone (by rw [if_neg hi])
  · exfalso
    by_cases hi : T.idx v = n
    · obtain ⟨hdt, hit⟩ := T.dir_walk_forward p (n - 1) (by omega)
      obtain ⟨hdg, hig⟩ := T.dir_walk_backward v (n - 1) (by omega)
      have hig1 : T.idx (walk v (T.dir v) (-((n - 1 : ℕ) : ℤ))) = 1 := by rw [hig, hi]; omega
      have hgt : walk v (T.dir v) (-((n - 1 : ℕ) : ℤ))
          = nbr (walk p (T.dir p) ((n - 1 : ℕ) : ℤ)) (T.dir p + 5) := by
        rw [hk, hvdef]
        simp only [walk, nbr, vec_add_three, smul_neg, neg_smul, neg_neg]
        abel
      have hxt : T.label (walk p (T.dir p) ((n - 1 : ℕ) : ℤ)) (T.dir p + 5) = some .x2 := by
        rw [T.label_shift5 (u := T.dir p) (k := 0) (by rw [hdt, add_zero])
          (by decide : (5 : HexDir) = 0 + 5), if_pos (by omega)]
      have hag : T.label (walk v (T.dir v) (-((n - 1 : ℕ) : ℤ))) (T.dir p + 2) = some (.a 1) := by
        rw [T.label_shift5 (u := T.dir p) (k := 3) (by rw [hdg, hk])
          (by decide : (2 : HexDir) = 3 + 5), if_neg (by omega), hig1]
      exact T.clash hv hxt (by rw [← hgt, opp_add_five]; exact hag)
        (Or.inl (ForbiddenCore.rule8 (le_refl 1) (by omega)))
    · have hs : nbr v (T.dir v) = nbr p (T.dir p + 4) := by
        rw [hk]; exact nbr_nbr_of_vec p (vec_five_three _)
      have hds : T.dir (nbr v (T.dir v)) = T.dir v := T.succ_dir v (by omega)
      have his : T.idx (nbr v (T.dir v)) = T.idx v + 1 := T.succ_idx v (by omega)
      have hbs : T.label (nbr v (T.dir v)) (T.dir p + 1) = some (.b (T.idx v)) := by
        rw [T.label_shift4 (u := T.dir p) (k := 3) (by rw [hds, hk])
          (by decide : (1 : HexDir) = 3 + 4), if_neg (by omega), his]
        simp
      have hz1 : T.label p (T.dir p + 4) = some .z1 := by
        rw [T.label_dir_add_four, if_pos hp]
      have hpnbr : nbr (nbr v (T.dir v)) (T.dir p + 1) = p := by
        rw [hs]
        exact nbr_nbr_cancel p (opp_add_four (T.dir p)).symm
      exact T.clash hv hbs (by rw [hpnbr, opp_add_one]; exact hz1)
        (Or.inr (ForbiddenCore.rule9 hposv (by omega)))
  · refine Or.inr (Or.inr ⟨by rw [hk, opp_add_one], ?_⟩)
    rw [T.label_shift3 hk (by decide : (1 : HexDir) = 4 + 3)] at hbnone
    by_contra hi
    exact hbnone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift3 hk (by decide : (2 : HexDir) = 5 + 3)] at haface hanone
    by_cases hi : T.idx v = 1
    · exact haface .y1 (by rw [if_pos hi])
        (Or.inr (ForbiddenCore.rule5 (Or.inl rfl) (Or.inl rfl)))
    · exact hanone (by rw [if_neg hi])

/-- A back corner of a stick which lies just beyond the tail of a parallel stick is covered by
the *first* cell of a stick pointing in the direction `dir p + 5`. -/
lemma corner_beyond_tail (hv : T.SatisfiesWeaveRules) {p : Hex} (hp : T.idx p < n)
    (hq : T.dir (nbr (nbr p (T.dir p + 5)) (T.dir p + 3)) = T.dir p)
    (hqi : T.idx (nbr (nbr p (T.dir p + 5)) (T.dir p + 3)) = n) :
    T.dir (nbr p (T.dir p + 5)) = T.dir p + 5 ∧ T.idx (nbr p (T.dir p + 5)) = 1 := by
  set z := nbr p (T.dir p + 5) with hzdef
  have hqz : nbr (nbr z (T.dir p + 3)) (T.dir p + 0) = z :=
    nbr_nbr_cancel z (opp_add_three' (T.dir p)).symm
  have hy2 : T.label (nbr z (T.dir p + 3)) (T.dir p + 0) = some .y2 := by
    rw [T.label_shift0 (u := T.dir p) (k := 0) (by rw [hq, add_zero])
      (by decide : (0 : HexDir) = 0), if_pos hqi]
  have hyface : ∀ Q, T.label z (T.dir p + 3) = some Q → ¬ Forbidden n .y2 Q := fun Q hQ hf =>
    T.clash hv hy2 (by rw [hqz, opp_add_zero']; exact hQ) hf
  have hynone : T.label z (T.dir p + 3) ≠ none := fun h =>
    T.no_none hy2 (by rw [hqz, opp_add_zero']; exact h)
  have ha : T.label p (T.dir p + 5) = some (.a (T.idx p)) := by
    rw [T.label_dir_add_five, if_neg (by omega)]
  have haface : ∀ Q, T.label z (T.dir p + 2) = some Q → ¬ Forbidden n (.a (T.idx p)) Q :=
    fun Q hQ hf => T.clash hv ha (by rw [opp_add_five]; exact hQ) hf
  have hanone : T.label z (T.dir p + 2) ≠ none := fun h =>
    T.no_none ha (by rw [opp_add_five]; exact h)
  have hpz : nbr (nbr p (T.dir p)) (T.dir p + 4) = z := nbr_nbr_of_vec p (vec_zero_four _)
  have hd2 : T.dir (nbr p (T.dir p)) = T.dir p := T.succ_dir p hp
  have hi2 : T.idx (nbr p (T.dir p)) = T.idx p + 1 := T.succ_idx p hp
  obtain ⟨B, hB⟩ : ∃ B, T.label (nbr p (T.dir p)) (T.dir p + 4) = some B := by
    rw [T.label_shift4 (u := T.dir p) (k := 0) (by rw [hd2, add_zero])
      (by decide : (4 : HexDir) = 0 + 4)]
    split <;> exact ⟨_, rfl⟩
  have hbnone : T.label z (T.dir p + 1) ≠ none := fun h =>
    T.no_none hB (by rw [hpz, opp_add_four]; exact h)
  have hposz := T.idx_pos z
  have hlez := T.idx_le z
  rcases hexDir_cases (T.dir p) (T.dir z) with hk | hk | hk | hk | hk | hk
  · exfalso
    have hd0 : T.dir z = T.dir p + 0 := by rw [hk, add_zero]
    rw [T.label_shift3 hd0 (by decide : (3 : HexDir) = 0 + 3)] at hyface hynone
    by_cases hi : T.idx z = 1
    · exact hyface .y1 (by rw [if_pos hi]) (forbidden_of_isY_isY (Or.inr rfl) (Or.inl rfl))
    · exact hynone (by rw [if_neg hi])
  · exfalso
    rw [T.label_shift2 hk (by decide : (3 : HexDir) = 1 + 2)] at hyface hynone
    rw [T.label_shift0 hk (by decide : (1 : HexDir) = 1)] at hbnone
    by_cases hi : T.idx z = 1
    · exact hyface .x1 (by rw [if_pos hi])
        (Or.inl (ForbiddenCore.rule3 (Or.inr rfl) (Or.inl rfl)))
    · by_cases hi' : T.idx z = n
      · refine hyface (.c 1) ?_ (Or.inl (ForbiddenCore.rule5 (Or.inr rfl) (Or.inr rfl)))
        rw [if_neg hi, hi', show n + 1 - n = 1 from by omega]
      · exact hbnone (by rw [if_neg hi'])
  · exfalso
    rw [T.label_shift1 hk (by decide : (3 : HexDir) = 2 + 1)] at hyface hynone
    rw [T.label_shift0 hk (by decide : (2 : HexDir) = 2)] at hanone
    by_cases hi' : T.idx z = n
    · exact hyface .z2 (by rw [if_pos hi']) (Or.inl (ForbiddenCore.rule10 (Or.inr rfl)))
    · by_cases hi : T.idx z = 1
      · refine hyface (.d (n - 1)) ?_ (Or.inl (ForbiddenCore.rule11 (Or.inr rfl)))
        rw [if_neg hi', hi]
      · exact hanone (by rw [if_neg hi'])
  · exfalso
    rw [T.label_shift0 hk (by decide : (3 : HexDir) = 3)] at hyface hynone
    by_cases hi' : T.idx z = n
    · exact hyface .y2 (by rw [if_pos hi']) (forbidden_of_isY_isY (Or.inr rfl) (Or.inr rfl))
    · exact hynone (by rw [if_neg hi'])
  · exfalso
    rw [T.label_shift5 hk (by decide : (3 : HexDir) = 4 + 5)] at hyface hynone
    rw [T.label_shift3 hk (by decide : (1 : HexDir) = 4 + 3)] at hbnone
    by_cases hi' : T.idx z = n
    · exact hyface .x2 (by rw [if_pos hi'])
        (Or.inl (ForbiddenCore.rule3 (Or.inr rfl) (Or.inr rfl)))
    · by_cases hi : T.idx z = 1
      · refine hyface (.a 1) ?_ (Or.inl (ForbiddenCore.rule5 (Or.inr rfl) (Or.inl rfl)))
        rw [if_neg hi', hi]
      · exact hbnone (by rw [if_neg hi])
  · rw [T.label_shift3 hk (by decide : (2 : HexDir) = 5 + 3)] at haface hanone
    refine ⟨hk, ?_⟩
    by_contra hi
    exact hanone (by rw [if_neg hi])

end StickTiling

end StickPolyhex
