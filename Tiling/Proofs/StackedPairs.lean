import Tiling.Proofs.ValidTilings

/-!
# Stacked pairs of sticks

This file formalises the notion of a *stacked pair* of sticks, and the distinction between
*left-leaning* and *right-leaning* stacked pairs, from the paper, and proves the first step of
the proof of Lemma 4: the cells immediately beyond the two ends of a stick belonging to a
stacked pair are covered by sticks whose axis is the direction in which the pair is stacked.

## Main definitions

* `SameAxis d e`: the directions `d` and `e` span the same axis, i.e. `e = d` or `e = -d`.
* `StickTiling.StackedBy T c c' e`: the stick through `c'` is the stick through `c` translated by
  the unit vector `e`, which is not parallel to the common axis of the two sticks.  This is the
  paper's notion of a *stacked pair*: see `StickTiling.stackedBy_iff_fillsCorners` in
  `Tiling/Proofs/CornerCells.lean`, which shows that it is equivalent to asking that the two
  sticks have the same axis and that one of them fills all the concave corners on one side of
  the other.
* `StickTiling.LeansLeft`, `StickTiling.LeansRight`: the two possible ways a stacked pair can
  lean.  With the convention that `HexDir.NE` points up and to the right, a pair of horizontal
  sticks whose upper stick is shifted to the left leans left; this is invariant under rotation.

## Main results

* `StickTiling.sameAxis_dir_nbr_tail_of_stackedBy` and
  `StickTiling.sameAxis_dir_nbr_head_of_stackedBy`: the case analysis of Lemma 4, and
  `StickTiling.sameAxis_dir_nbr_ends_of_stackedBy`, which combines them.
* `StickTiling.leansLeft_or_leansRight`, `StickTiling.not_leansLeft_and_leansRight`: every
  stacked pair leans in exactly one of the two ways.
-/

namespace StickPolyhex

/-- Two directions span the same axis: they are equal or opposite. -/
def SameAxis (d e : HexDir) : Prop := e = d ∨ e = d.opp

instance (d e : HexDir) : Decidable (SameAxis d e) :=
  inferInstanceAs (Decidable (e = d ∨ e = d.opp))

lemma sameAxis_self (d : HexDir) : SameAxis d d := Or.inl rfl

lemma SameAxis.symm {d e : HexDir} (h : SameAxis d e) : SameAxis e d := by
  revert h; revert d e; decide

lemma SameAxis.opp_left {d e : HexDir} (h : SameAxis d e) : SameAxis d.opp e := by
  revert h; revert d e; decide

lemma sameAxis_comm {d e : HexDir} : SameAxis d e ↔ SameAxis e d :=
  ⟨SameAxis.symm, SameAxis.symm⟩

/-- Adding a unit vector to a neighbouring unit vector. -/
lemma nbr_nbr_of_vec (c : Hex) {a b f : HexDir} (h : a.vec + b.vec = f.vec) :
    nbr (nbr c a) b = nbr c f := by
  simp [nbr, add_assoc, h]

lemma walk_inj (c : Hex) (d : HexDir) {k l : ℤ} (h : walk c d k = walk c d l) : k = l := by
  have h' : k • d.vec = l • d.vec := by
    simpa [walk] using h
  have := HexDir.vec_ne_zero d
  exact smul_left_injective ℤ this h'

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Cells of a stick -/

lemma dir_of_mem_stickOf {c x : Hex} (h : x ∈ T.stickOf c) : T.dir x = T.dir c := by
  rw [mem_stickOf_iff] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact T.cellOfStick_dir c k hk

lemma nbr_dir_mem_stickOf (c : Hex) (h : T.idx c < n) : nbr c (T.dir c) ∈ T.stickOf c := by
  have hpos := T.idx_pos c
  refine (T.mem_stickOf_iff c _).2 ⟨T.idx c, h, ?_⟩
  have hc : T.cellOfStick c (T.idx c - 1) = c := T.cellOfStick_idx_sub_one c
  have hcast : ((T.idx c : ℕ) : ℤ) = ((T.idx c - 1 : ℕ) : ℤ) + 1 := by omega
  rw [cellOfStick, hcast, ← walk_walk, ← cellOfStick, hc, nbr_eq_walk_one]

lemma nbr_dir_opp_mem_stickOf (c : Hex) (h : 1 < T.idx c) :
    nbr c (T.dir c).opp ∈ T.stickOf c := by
  have hle := T.idx_le c
  refine (T.mem_stickOf_iff c _).2 ⟨T.idx c - 2, by omega, ?_⟩
  have hc : T.cellOfStick c (T.idx c - 1) = c := T.cellOfStick_idx_sub_one c
  have hcast : ((T.idx c - 2 : ℕ) : ℤ) = ((T.idx c - 1 : ℕ) : ℤ) + (-1) := by omega
  rw [cellOfStick, hcast, ← walk_walk, ← cellOfStick, hc, nbr_eq_walk_one, walk_opp]

lemma nbr_dir_not_mem_stickOf {c : Hex} (h : T.idx c = n) : nbr c (T.dir c) ∉ T.stickOf c := by
  intro hmem
  have hpos := T.idx_pos c
  rw [mem_stickOf_iff] at hmem
  obtain ⟨k, hk, hkc⟩ := hmem
  have hc : walk (T.head c) (T.dir c) ((n - 1 : ℕ) : ℤ) = c := by
    have h0 := T.cellOfStick_idx_sub_one c
    rw [h] at h0
    exact h0
  have h1 : nbr c (T.dir c) = walk (T.head c) (T.dir c) ((n : ℤ)) := by
    calc nbr c (T.dir c) = walk c (T.dir c) 1 := nbr_eq_walk_one _ _
      _ = walk (walk (T.head c) (T.dir c) ((n - 1 : ℕ) : ℤ)) (T.dir c) 1 := by rw [hc]
      _ = walk (T.head c) (T.dir c) (((n - 1 : ℕ) : ℤ) + 1) := walk_walk _ _ _ _
      _ = walk (T.head c) (T.dir c) ((n : ℤ)) := by congr 1; omega
  rw [h1, cellOfStick] at hkc
  have := walk_inj (T.head c) (T.dir c) hkc
  omega

lemma nbr_dir_opp_not_mem_stickOf {c : Hex} (h : T.idx c = 1) :
    nbr c (T.dir c).opp ∉ T.stickOf c := by
  intro hmem
  rw [mem_stickOf_iff] at hmem
  obtain ⟨k, hk, hkc⟩ := hmem
  have hc : T.head c = c := by
    have := T.cellOfStick_idx_sub_one c
    rw [h] at this
    simpa [cellOfStick] using this
  have h1 : nbr c (T.dir c).opp = walk (T.head c) (T.dir c) (-1) := by
    rw [nbr_eq_walk_one, walk_opp, hc]
  rw [cellOfStick, h1] at hkc
  have := walk_inj (T.head c) (T.dir c) hkc
  omega

/-! ### Computing labels relative to the orientation of a stick -/

lemma label_dir_add (c : Hex) (k : HexDir) :
    T.label c (T.dir c + k) = frameLabel n (T.idx c) (k + HexDir.W) := by
  rw [label]
  congr 1
  ring

lemma label_dir_add_one (c : Hex) :
    T.label c (T.dir c + 1) =
      if T.idx c = n then some .z2 else some (.d (n - T.idx c)) := by
  rw [label_dir_add]
  exact frameLabel_SW n (T.idx c)

lemma label_dir_add_two (c : Hex) :
    T.label c (T.dir c + 2) =
      if T.idx c = 1 then some .x1 else some (.c (n + 1 - T.idx c)) := by
  rw [label_dir_add]
  exact frameLabel_SE n (T.idx c)

lemma label_dir_add_four (c : Hex) :
    T.label c (T.dir c + 4) =
      if T.idx c = 1 then some .z1 else some (.b (T.idx c - 1)) := by
  rw [label_dir_add]
  exact frameLabel_NE n (T.idx c)

lemma label_dir_add_five (c : Hex) :
    T.label c (T.dir c + 5) =
      if T.idx c = n then some .x2 else some (.a (T.idx c)) := by
  rw [label_dir_add]
  exact frameLabel_NW n (T.idx c)

end StickTiling

/-! ### Classes of edge labels, and the matchings the rules forbid between them -/

/-- The label is one of the two labels `yᵢ` on the short ends of a stick. -/
def IsY (p : StickEdge) : Prop := p = .y1 ∨ p = .y2

/-- The label is one of the two labels `xᵢ`. -/
def IsX (p : StickEdge) : Prop := p = .x1 ∨ p = .x2

/-- The label is one of the two labels `zᵢ`. -/
def IsZ (p : StickEdge) : Prop := p = .z1 ∨ p = .z2

lemma forbidden_of_isY_isY {n : ℕ} {p q : StickEdge} (hp : IsY p) (hq : IsY q) :
    Forbidden n p q := Or.inl (ForbiddenCore.rule1 hp hq)

lemma forbidden_of_isX_isY {n : ℕ} {p q : StickEdge} (hp : IsX p) (hq : IsY q) :
    Forbidden n p q := Or.inr (ForbiddenCore.rule3 hq hp)

lemma forbidden_of_z2_isY {n : ℕ} {q : StickEdge} (hq : IsY q) :
    Forbidden n .z2 q := Or.inr (ForbiddenCore.rule10 hq)

lemma forbidden_of_isX_isZ {n : ℕ} {p q : StickEdge} (hp : IsX p) (hq : IsZ q) :
    Forbidden n p q := Or.inl (ForbiddenCore.rule4 hp hq)

/-! ### Arithmetic of directions -/

lemma add_one_five (a : HexDir) : a + 1 + 5 = a := by revert a; decide
lemma add_two_four (a : HexDir) : a + 2 + 4 = a := by revert a; decide
lemma add_four_two (a : HexDir) : a + 4 + 2 = a := by revert a; decide
lemma add_five_one (a : HexDir) : a + 5 + 1 = a := by revert a; decide
lemma opp_eq_add_three (a : HexDir) : a.opp = a + 3 := rfl

lemma hexDir_cases (a b : HexDir) :
    b = a ∨ b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b = a + 4 ∨ b = a + 5 := by
  revert a b; decide

lemma sameAxis_add_three (a : HexDir) : SameAxis (a + 3) a := by revert a; decide

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### The two basic case analyses

These are the two configurations that occur next to a stacked pair: a cell `x` whose neighbour
in some direction `w` is the end of a stick (so presents a `y` label to `x`), and which has a
second constrained neighbour, either in direction `w + 1` or in direction `w - 1`.  In both
cases the orientation of the stick covering `x` is pinned down to a single axis. -/

/-- A cell whose neighbour presents a `y` label to it is covered by a stick that is not parallel
to the direction of that neighbour: two sticks may not meet end to end (rule 1). -/
lemma not_sameAxis_dir_of_label_isY (hv : T.SatisfiesWeaveRules) {x : Hex} {w : HexDir} {q : StickEdge}
    (hq : T.label (nbr x w) w.opp = some q) (hqy : IsY q) : ¬ SameAxis w (T.dir x) := by
  have hnone : T.label x w ≠ none := by
    intro h
    rw [(T.label_eq_none_comm x w).1 h] at hq
    exact absurd hq.symm (Option.some_ne_none q)
  rintro (h | h)
  · have hlab : T.label x w = if T.idx x = n then some .y2 else none := by
      rw [← h]; exact T.label_dir x
    by_cases hi : T.idx x = n
    · rw [if_pos hi] at hlab
      exact hv x w _ q hlab hq (forbidden_of_isY_isY (Or.inr rfl) hqy)
    · rw [if_neg hi] at hlab; exact hnone hlab
  · have hw : w = (T.dir x).opp := by rw [h]; simp
    have hlab : T.label x w = if T.idx x = 1 then some .y1 else none := by
      rw [hw]; exact T.label_opp_dir x
    by_cases hi : T.idx x = 1
    · rw [if_pos hi] at hlab
      exact hv x w _ q hlab hq (forbidden_of_isY_isY (Or.inl rfl) hqy)
    · rw [if_neg hi] at hlab; exact hnone hlab

/-- **First case analysis.**  Suppose the neighbour of `x` in direction `w` presents a `y` label
to `x` (so that neighbour is the end cell of its stick, facing `x`), and the neighbour of `x` in
direction `w + 1` is not part of the stick covering `x`.  Then the stick covering `x` has axis
`w + 2`. -/
theorem sameAxis_dir_of_shallow_add (hv : T.SatisfiesWeaveRules) {x : Hex} {w : HexDir} {q : StickEdge}
    (hq : T.label (nbr x w) w.opp = some q) (hqy : IsY q) (hne : T.label x (w + 1) ≠ none) :
    SameAxis (w + 2) (T.dir x) := by
  have hnp := T.not_sameAxis_dir_of_label_isY hv hq hqy
  rcases hexDir_cases (T.dir x) w with h | h | h | h | h | h
  · exact absurd (Or.inl h.symm) hnp
  · -- `w = dir x + 1`, i.e. `dir x = w + 5`
    subst h
    exact (by decide : ∀ a : HexDir, SameAxis (a + 1 + 2) a) (T.dir x)
  · -- `w = dir x + 2`, i.e. `dir x = w + 4`
    exfalso
    have h1 : w + 1 = (T.dir x).opp := by
      rw [h, opp_eq_add_three]
      exact (by decide : ∀ a : HexDir, a + 2 + 1 = a + 3) (T.dir x)
    have hlab1 : T.label x (w + 1) = if T.idx x = 1 then some .y1 else none := by
      rw [h1]; exact T.label_opp_dir x
    by_cases hi : T.idx x = 1
    · have hlab : T.label x w = some .x1 := by
        rw [h, T.label_dir_add_two, if_pos hi]
      exact hv x w _ q hlab hq (forbidden_of_isX_isY (Or.inl rfl) hqy)
    · rw [if_neg hi] at hlab1; exact hne hlab1
  · refine absurd (Or.inr ?_) hnp
    rw [opp_eq_add_three, h]
    exact (by decide : ∀ a : HexDir, a = a + 3 + 3) (T.dir x)
  · -- `w = dir x + 4`, i.e. `dir x = w + 2`
    exact Or.inl (by rw [h, add_four_two])
  · -- `w = dir x + 5`, i.e. `dir x = w + 1`
    exfalso
    have h1 : w + 1 = T.dir x := by rw [h, add_five_one]
    have hlab1 : T.label x (w + 1) = if T.idx x = n then some .y2 else none := by
      rw [h1]; exact T.label_dir x
    by_cases hi : T.idx x = n
    · have hlab : T.label x w = some .x2 := by
        rw [h, T.label_dir_add_five, if_pos hi]
      exact hv x w _ q hlab hq (forbidden_of_isX_isY (Or.inr rfl) hqy)
    · rw [if_neg hi] at hlab1; exact hne hlab1

/-- **Second case analysis.**  Suppose the neighbour of `x` in direction `w` presents a `y` label
to `x`, and the neighbour of `x` in direction `w - 1` presents an `x` label to `x`.  Then the
stick covering `x` has axis `w + 1`. -/
theorem sameAxis_dir_of_shallow_sub (hv : T.SatisfiesWeaveRules) {x : Hex} {w : HexDir} {q r : StickEdge}
    (hq : T.label (nbr x w) w.opp = some q) (hqy : IsY q)
    (hr : T.label (nbr x (w + 5)) (w + 5).opp = some r) (hrx : IsX r) :
    SameAxis (w + 1) (T.dir x) := by
  have hnp := T.not_sameAxis_dir_of_label_isY hv hq hqy
  have hne : T.label x (w + 5) ≠ none := by
    intro h
    rw [(T.label_eq_none_comm x (w + 5)).1 h] at hr
    exact absurd hr.symm (Option.some_ne_none r)
  rcases hexDir_cases (T.dir x) w with h | h | h | h | h | h
  · exact absurd (Or.inl h.symm) hnp
  · -- `w = dir x + 1`, i.e. `dir x = w + 5`: the stick through `x` ends at `x` and presents
    -- the label `z₂` to its `w`-neighbour, which rule 10 forbids.
    exfalso
    have h1 : w + 5 = T.dir x := by
      rw [h]; exact (by decide : ∀ a : HexDir, a + 1 + 5 = a) (T.dir x)
    have hlab1 : T.label x (w + 5) = if T.idx x = n then some .y2 else none := by
      rw [h1]; exact T.label_dir x
    by_cases hi : T.idx x = n
    · have hlab : T.label x w = some .z2 := by
        rw [h, T.label_dir_add_one, if_pos hi]
      exact hv x w _ q hlab hq (forbidden_of_z2_isY hqy)
    · rw [if_neg hi] at hlab1; exact hne hlab1
  · -- `w = dir x + 2`, i.e. `dir x = w + 4`
    subst h
    exact (by decide : ∀ a : HexDir, SameAxis (a + 2 + 1) a) (T.dir x)
  · refine absurd (Or.inr ?_) hnp
    rw [opp_eq_add_three, h]
    exact (by decide : ∀ a : HexDir, a = a + 3 + 3) (T.dir x)
  · -- `w = dir x + 4`, i.e. `dir x = w + 2`: the stick through `x` ends at `x`, presenting a
    -- `y` label to the cell in direction `w - 1`, which carries an `x` label: rule 3.
    exfalso
    have h1 : w + 5 = (T.dir x).opp := by
      rw [h, opp_eq_add_three]
      exact (by decide : ∀ a : HexDir, a + 4 + 5 = a + 3) (T.dir x)
    have hlab1 : T.label x (w + 5) = if T.idx x = 1 then some .y1 else none := by
      rw [h1]; exact T.label_opp_dir x
    by_cases hi : T.idx x = 1
    · rw [if_pos hi] at hlab1
      exact hv x (w + 5) _ r hlab1 hr ((forbidden_of_isX_isY hrx (Or.inl rfl)).symm)
    · rw [if_neg hi] at hlab1; exact hne hlab1
  · -- `w = dir x + 5`, i.e. `dir x = w + 1`
    subst h
    exact (by decide : ∀ a : HexDir, SameAxis (a + 5 + 1) a) (T.dir x)

/-! ### Ends of sticks: the labels they present -/

lemma nbr_nbr_cancel (c : Hex) {a b : HexDir} (h : b = a.opp) : nbr (nbr c a) b = c := by
  rw [h]; exact nbr_opp_nbr c a

lemma nbr_comm (c : Hex) (a b : HexDir) : nbr (nbr c a) b = nbr (nbr c b) a := by
  simp [nbr, add_right_comm]

lemma sameAxis_trans_axis {a b v : HexDir} (hab : SameAxis a b) (h : SameAxis a v) :
    SameAxis b v := by
  revert hab h; revert a b v; decide

/-- A cell `u` whose stick ends at `u` in direction `m`: either the stick is oriented along `m`
and `u` is its last cell, or it is oriented against `m` and `u` is its first cell. -/
def EndsAt (u : Hex) (m : HexDir) : Prop :=
  (T.dir u = m ∧ T.idx u = n) ∨ (T.dir u = m.opp ∧ T.idx u = 1)

lemma EndsAt.label_isY {u : Hex} {m : HexDir} (h : T.EndsAt u m) :
    ∃ q, T.label u m = some q ∧ IsY q := by
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · exact ⟨.y2, by rw [← hd, T.label_dir u, if_pos hi], Or.inr rfl⟩
  · refine ⟨.y1, ?_, Or.inl rfl⟩
    have hm : m = (T.dir u).opp := by rw [hd]; simp
    rw [hm, T.label_opp_dir u, if_pos hi]

lemma EndsAt.label_isX {u : Hex} {m : HexDir} (h : T.EndsAt u m) :
    ∃ r, T.label u (m + 5) = some r ∧ IsX r := by
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · refine ⟨.x2, ?_, Or.inr rfl⟩
    rw [show m + 5 = T.dir u + 5 by rw [hd], T.label_dir_add_five u, if_pos hi]
  · refine ⟨.x1, ?_, Or.inl rfl⟩
    have hm : m + 5 = T.dir u + 2 := by
      rw [hd, opp_eq_add_three]
      exact (by decide : ∀ a : HexDir, a + 5 = a + 3 + 2) m
    rw [hm, T.label_dir_add_two u, if_pos hi]

lemma EndsAt.label_isZ {u : Hex} {m : HexDir} (h : T.EndsAt u m) :
    ∃ r, T.label u (m + 1) = some r ∧ IsZ r := by
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · refine ⟨.z2, ?_, Or.inr rfl⟩
    rw [show m + 1 = T.dir u + 1 by rw [hd], T.label_dir_add_one u, if_pos hi]
  · refine ⟨.z1, ?_, Or.inl rfl⟩
    have hm : m + 1 = T.dir u + 4 := by
      rw [hd, opp_eq_add_three]
      exact (by decide : ∀ a : HexDir, a + 1 = a + 3 + 4) m
    rw [hm, T.label_dir_add_four u, if_pos hi]

lemma endsAt_of_label_ne_none {u : Hex} {k : HexDir} (hax : SameAxis k (T.dir u))
    (hne : T.label u k ≠ none) : T.EndsAt u k := by
  rcases hax with h | h
  · left
    refine ⟨h, ?_⟩
    by_contra hi
    have : T.label u k = none := by
      rw [← h, T.label_dir u, if_neg hi]
    exact hne this
  · right
    refine ⟨h, ?_⟩
    by_contra hi
    have hk : k = (T.dir u).opp := by rw [h]; simp
    have : T.label u k = none := by
      rw [hk, T.label_opp_dir u, if_neg hi]
    exact hne this

lemma dir_nbr_of_label_eq_none {u : Hex} {k : HexDir} (h : T.label u k = none) :
    T.dir (nbr u k) = T.dir u := by
  rcases (T.label_eq_none_iff u k).1 h with ⟨rfl, hi⟩ | ⟨rfl, hi⟩
  · exact T.pred_dir u hi
  · exact T.succ_dir u hi

/-! ### The step that carries the analysis past the end of the partner stick -/

/-- If the stick through `u` has axis `k` and the cell in direction `k - 1` from `u` presents a
`z` label, then the stick through `u` continues to the cell in direction `k`: otherwise `u`
would present an `x` label to that `z` label, which rule 4 forbids. -/
lemma dir_nbr_eq_of_isZ (hv : T.SatisfiesWeaveRules) {u : Hex} {k : HexDir} {z : StickEdge}
    (hax : SameAxis k (T.dir u)) (hz : T.label (nbr u (k + 5)) (k + 5).opp = some z)
    (hzz : IsZ z) : T.dir (nbr u k) = T.dir u := by
  by_cases hnone : T.label u k = none
  · exact T.dir_nbr_of_label_eq_none hnone
  · exfalso
    obtain ⟨r, hr, hrx⟩ := (T.endsAt_of_label_ne_none hax hnone).label_isX
    exact hv u (k + 5) r z hr hz (forbidden_of_isX_isZ hrx hzz)

/-- If the stick through `u` has axis `k` and the cell in direction `k + 1` from `u` presents an
`x` label, then the stick through `u` continues to the cell in direction `k`. -/
lemma dir_nbr_eq_of_isX (hv : T.SatisfiesWeaveRules) {u : Hex} {k : HexDir} {r : StickEdge}
    (hax : SameAxis k (T.dir u)) (hr : T.label (nbr u (k + 1)) (k + 1).opp = some r)
    (hrx : IsX r) : T.dir (nbr u k) = T.dir u := by
  by_cases hnone : T.label u k = none
  · exact T.dir_nbr_of_label_eq_none hnone
  · exfalso
    obtain ⟨z, hz, hzz⟩ := (T.endsAt_of_label_ne_none hax hnone).label_isZ
    exact hv u (k + 1) z r hz hr (forbidden_of_isX_isZ hrx hzz).symm

/-! ### Stacked pairs -/

/-- `T.StackedBy c c' e`: the sticks through `c` and `c'` form a *stacked pair*, the stick
through `c'` being the stick through `c` translated by one step in the direction `e`, which is
not parallel to the axis of the two sticks.

This is the notion of the paper: two sticks with the same orientation modulo `π` such that one
of them fills all the concave corners on one side of the other. -/
def StackedBy (c c' : Hex) (e : HexDir) : Prop :=
  ¬ SameAxis (T.dir c) e ∧ SameAxis (T.dir c) (T.dir c') ∧
    ∀ x ∈ T.stickOf c, nbr x e ∈ T.stickOf c'

/-- Two sticks form a stacked pair if one is a translate of the other by a direction that is not
parallel to their common axis. -/
def IsStackedPair (c c' : Hex) : Prop := ∃ e, T.StackedBy c c' e

/-- The stick through `c'` really is the translate of the stick through `c`. -/
lemma stickOf_eq_image_of_stackedBy {c c' : Hex} {e : HexDir} (hst : T.StackedBy c c' e) :
    T.stickOf c' = (T.stickOf c).image (fun x => nbr x e) := by
  have hinj : Function.Injective (fun x : Hex => nbr x e) := by
    intro a b hab
    simpa [nbr] using hab
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact hst.2.2 z hz
  · rw [T.card_stickOf, Finset.card_image_of_injective _ hinj, T.card_stickOf]

/-- The partner of the last cell of a stick is the end cell of the partner stick: the stick
through it ends there, in the direction of the original stick. -/
lemma endsAt_nbr_of_stackedBy_tail {t c' : Hex} {e : HexDir} (hst : T.StackedBy t c' e)
    (ht : T.idx t = n) : T.EndsAt (nbr t e) (T.dir t) := by
  have hmem : nbr t e ∈ T.stickOf c' := hst.2.2 t (T.self_mem_stickOf t)
  have hstick : T.stickOf (nbr t e) = T.stickOf c' := T.stickOf_eq_of_mem hmem
  have hdir : T.dir (nbr t e) = T.dir c' := T.dir_of_mem_stickOf hmem
  have hax : SameAxis (T.dir t) (T.dir (nbr t e)) := by rw [hdir]; exact hst.2.1
  have hnot : nbr (nbr t e) (T.dir t) ∉ T.stickOf (nbr t e) := by
    rw [hstick, T.stickOf_eq_image_of_stackedBy hst]
    intro hmem2
    simp only [Finset.mem_image] at hmem2
    obtain ⟨z, hz, hze⟩ := hmem2
    have hz' : z = nbr t (T.dir t) := by
      have : nbr z e = nbr (nbr t (T.dir t)) e := by
        rw [hze, nbr_comm]
      simpa [nbr] using this
    rw [hz'] at hz
    exact T.nbr_dir_not_mem_stickOf ht hz
  rcases hax with h | h
  · refine Or.inl ⟨h, ?_⟩
    by_contra hi
    exact hnot (by rw [← h]; exact T.nbr_dir_mem_stickOf _ (lt_of_le_of_ne (T.idx_le _) hi))
  · refine Or.inr ⟨h, ?_⟩
    by_contra hi
    have hlt : 1 < T.idx (nbr t e) := lt_of_le_of_ne (T.idx_pos _) (Ne.symm hi)
    have := T.nbr_dir_opp_mem_stickOf _ hlt
    rw [h] at this
    simp only [HexDir.opp_opp] at this
    exact hnot this

/-- The partner of the first cell of a stick is the end cell of the partner stick. -/
lemma endsAt_nbr_of_stackedBy_head {h0 c' : Hex} {e : HexDir} (hst : T.StackedBy h0 c' e)
    (hh : T.idx h0 = 1) : T.EndsAt (nbr h0 e) (T.dir h0).opp := by
  have hmem : nbr h0 e ∈ T.stickOf c' := hst.2.2 h0 (T.self_mem_stickOf h0)
  have hstick : T.stickOf (nbr h0 e) = T.stickOf c' := T.stickOf_eq_of_mem hmem
  have hdir : T.dir (nbr h0 e) = T.dir c' := T.dir_of_mem_stickOf hmem
  have hax : SameAxis (T.dir h0) (T.dir (nbr h0 e)) := by rw [hdir]; exact hst.2.1
  have hnot : nbr (nbr h0 e) (T.dir h0).opp ∉ T.stickOf (nbr h0 e) := by
    rw [hstick, T.stickOf_eq_image_of_stackedBy hst]
    intro hmem2
    simp only [Finset.mem_image] at hmem2
    obtain ⟨z, hz, hze⟩ := hmem2
    have hz' : z = nbr h0 (T.dir h0).opp := by
      have : nbr z e = nbr (nbr h0 (T.dir h0).opp) e := by
        rw [hze, nbr_comm]
      simpa [nbr] using this
    rw [hz'] at hz
    exact T.nbr_dir_opp_not_mem_stickOf hh hz
  rcases hax with h | h
  · refine Or.inr ⟨by rw [h]; simp, ?_⟩
    by_contra hi
    have hlt : 1 < T.idx (nbr h0 e) := lt_of_le_of_ne (T.idx_pos _) (Ne.symm hi)
    have := T.nbr_dir_opp_mem_stickOf _ hlt
    rw [h] at this
    exact hnot this
  · refine Or.inl ⟨h, ?_⟩
    by_contra hi
    have := T.nbr_dir_mem_stickOf _ (lt_of_le_of_ne (T.idx_le _) hi)
    rw [h] at this
    exact hnot this

/-! ### The case analysis of Lemma 4

If a stick belongs to a stacked pair, then the cell immediately beyond either of its two ends is
covered by a stick whose axis is the direction in which the pair is stacked.  Some of the cases
are illustrated in Figure 6 of the paper. -/

/-- **Lemma 4, first step, at the far end of a stick.**  If the stick through the cell `t`
(of which `t` is the last cell) is stacked with another stick by the translation `e`, then the
cell immediately beyond `t` is covered by a stick whose axis is `e`. -/
theorem sameAxis_dir_nbr_tail_of_stackedBy (hv : T.SatisfiesWeaveRules) {t c' : Hex} {e : HexDir}
    (ht : T.idx t = n) (hst : T.StackedBy t c' e) :
    SameAxis e (T.dir (nbr t (T.dir t))) := by
  set d := T.dir t with hd
  have hbend : T.EndsAt (nbr t e) d := T.endsAt_nbr_of_stackedBy_tail hst ht
  have htend : T.EndsAt t d := Or.inl ⟨rfl, ht⟩
  obtain ⟨qb, hqb, hqby⟩ := hbend.label_isY
  obtain ⟨rb, hrb, hrbx⟩ := hbend.label_isX
  obtain ⟨zb, hzb, hzbz⟩ := hbend.label_isZ
  obtain ⟨qt, hqt, hqty⟩ := htend.label_isY
  obtain ⟨rt, hrt, hrtx⟩ := htend.label_isX
  obtain ⟨zt, hzt, hztz⟩ := htend.label_isZ
  have hnpar := hst.1
  rw [← hd] at hnpar
  -- the cell beyond `t`
  have hopp3 : (d + 3).opp = d := (by decide : ∀ a : HexDir, (a + 3).opp = a) d
  rcases hexDir_cases d e with he | he | he | he | he | he
  · exact absurd (Or.inl he) hnpar
  · -- `e = d + 1`: the pair is stacked on the front side, and `t` is at the shallow end
    subst he
    have hbt : nbr (nbr t d) (d + 3 + 5) = nbr t (d + 1) := by
      rw [(by decide : ∀ a : HexDir, a + 3 + 5 = a + 2) d]
      exact nbr_nbr_of_vec t ((by decide : ∀ a : HexDir, a.vec + (a + 2).vec = (a + 1).vec) d)
    have hq : T.label (nbr (nbr t d) (d + 3)) (d + 3).opp = some qt := by
      rw [nbr_nbr_cancel t (rfl : d + 3 = d.opp), hopp3]; exact hqt
    have hr : T.label (nbr (nbr t d) (d + 3 + 5)) (d + 3 + 5).opp = some rb := by
      rw [hbt, (by decide : ∀ a : HexDir, (a + 3 + 5).opp = a + 5) d]; exact hrb
    exact sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 3 + 1) (a + 1)) d)
      (T.sameAxis_dir_of_shallow_sub hv hq hqty hr hrbx)
  · -- `e = d + 2`: `t` is at the deep end; we go through the cell `u` beyond the partner stick
    subst he
    -- the cell `nbr t (d + 1)` is the cell just beyond the end of the partner stick
    have hub : nbr (nbr t (d + 1)) (d + 3) = nbr t (d + 2) :=
      nbr_nbr_of_vec t ((by decide : ∀ a : HexDir, (a + 1).vec + (a + 3).vec = (a + 2).vec) d)
    have hut : nbr (nbr t (d + 1)) (d + 4) = t :=
      nbr_nbr_cancel t ((by decide : ∀ a : HexDir, a + 4 = (a + 1).opp) d)
    have hq : T.label (nbr (nbr t (d + 1)) (d + 3)) (d + 3).opp = some qb := by
      rw [hub, hopp3]; exact hqb
    have hne : T.label (nbr t (d + 1)) (d + 3 + 1) ≠ none := by
      rw [(by decide : ∀ a : HexDir, a + 3 + 1 = a + 4) d]
      intro hnone
      have h2 := (T.label_eq_none_comm (nbr t (d + 1)) (d + 4)).1 hnone
      rw [hut, (by decide : ∀ a : HexDir, (a + 4).opp = a + 1) d, hzt] at h2
      exact absurd h2 (Option.some_ne_none zt)
    have hax : SameAxis (d + 5) (T.dir (nbr t (d + 1))) :=
      sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 3 + 2) (a + 5)) d)
        (T.sameAxis_dir_of_shallow_add hv hq hqby hne)
    have hz : T.label (nbr (nbr t (d + 1)) (d + 5 + 5)) (d + 5 + 5).opp = some zt := by
      rw [(by decide : ∀ a : HexDir, a + 5 + 5 = a + 4) d, hut,
        (by decide : ∀ a : HexDir, (a + 4).opp = a + 1) d]
      exact hzt
    have hR : nbr (nbr t (d + 1)) (d + 5) = nbr t d :=
      nbr_nbr_of_vec t ((by decide : ∀ a : HexDir, (a + 1).vec + (a + 5).vec = a.vec) d)
    have hdir := T.dir_nbr_eq_of_isZ hv hax hz hztz
    rw [hR] at hdir
    rw [hdir]
    exact sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 5) (a + 2)) d) hax
  · exact absurd (Or.inr he) hnpar
  · -- `e = d + 4`: `t` is again at the deep end
    subst he
    -- the cell `nbr t (d + 5)` is the cell just beyond the end of the partner stick
    have hub : nbr (nbr t (d + 5)) (d + 3) = nbr t (d + 4) :=
      nbr_nbr_of_vec t ((by decide : ∀ a : HexDir, (a + 5).vec + (a + 3).vec = (a + 4).vec) d)
    have hut : nbr (nbr t (d + 5)) (d + 2) = t :=
      nbr_nbr_cancel t ((by decide : ∀ a : HexDir, a + 2 = (a + 5).opp) d)
    have hq : T.label (nbr (nbr t (d + 5)) (d + 3)) (d + 3).opp = some qb := by
      rw [hub, hopp3]; exact hqb
    have hr : T.label (nbr (nbr t (d + 5)) (d + 3 + 5)) (d + 3 + 5).opp = some rt := by
      rw [(by decide : ∀ a : HexDir, a + 3 + 5 = a + 2) d, hut,
        (by decide : ∀ a : HexDir, (a + 2).opp = a + 5) d]
      exact hrt
    have hax : SameAxis (d + 1) (T.dir (nbr t (d + 5))) :=
      sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 3 + 1) (a + 1)) d)
        (T.sameAxis_dir_of_shallow_sub hv hq hqby hr hrtx)
    have hx : T.label (nbr (nbr t (d + 5)) (d + 1 + 1)) (d + 1 + 1).opp = some rt := by
      rw [(by decide : ∀ a : HexDir, a + 1 + 1 = a + 2) d, hut,
        (by decide : ∀ a : HexDir, (a + 2).opp = a + 5) d]
      exact hrt
    have hR : nbr (nbr t (d + 5)) (d + 1) = nbr t d :=
      nbr_nbr_of_vec t ((by decide : ∀ a : HexDir, (a + 5).vec + (a + 1).vec = a.vec) d)
    have hdir := T.dir_nbr_eq_of_isX hv hax hx hrtx
    rw [hR] at hdir
    rw [hdir]
    exact sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 1) (a + 4)) d) hax
  · -- `e = d + 5`: the pair is stacked on the back side, and `t` is at the shallow end
    subst he
    have hbt : nbr (nbr t d) (d + 3 + 1) = nbr t (d + 5) := by
      rw [(by decide : ∀ a : HexDir, a + 3 + 1 = a + 4) d]
      exact nbr_nbr_of_vec t ((by decide : ∀ a : HexDir, a.vec + (a + 4).vec = (a + 5).vec) d)
    have hq : T.label (nbr (nbr t d) (d + 3)) (d + 3).opp = some qt := by
      rw [nbr_nbr_cancel t (rfl : d + 3 = d.opp), hopp3]; exact hqt
    have hne : T.label (nbr t d) (d + 3 + 1) ≠ none := by
      intro hnone
      have h2 := (T.label_eq_none_comm (nbr t d) (d + 3 + 1)).1 hnone
      rw [hbt, (by decide : ∀ a : HexDir, (a + 3 + 1).opp = a + 1) d, hzb] at h2
      exact absurd h2 (Option.some_ne_none zb)
    exact sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 3 + 2) (a + 5)) d)
      (T.sameAxis_dir_of_shallow_add hv hq hqty hne)

/-- **Lemma 4, first step, at the near end of a stick.**  If the stick through the cell `h0`
(of which `h0` is the first cell) is stacked with another stick by the translation `e`, then the
cell immediately beyond `h0` is covered by a stick whose axis is `e`. -/
theorem sameAxis_dir_nbr_head_of_stackedBy (hv : T.SatisfiesWeaveRules) {h0 c' : Hex} {e : HexDir}
    (hh : T.idx h0 = 1) (hst : T.StackedBy h0 c' e) :
    SameAxis e (T.dir (nbr h0 (T.dir h0).opp)) := by
  set d := T.dir h0 with hd
  have hbend : T.EndsAt (nbr h0 e) (d + 3) := by
    have := T.endsAt_nbr_of_stackedBy_head hst hh
    rwa [← hd, opp_eq_add_three] at this
  have htend : T.EndsAt h0 (d + 3) :=
    Or.inr ⟨(by decide : ∀ a : HexDir, a = (a + 3).opp) d, hh⟩
  obtain ⟨qb, hqb, hqby⟩ := hbend.label_isY
  obtain ⟨rb, hrb, hrbx⟩ := hbend.label_isX
  obtain ⟨zb, hzb, hzbz⟩ := hbend.label_isZ
  obtain ⟨qh, hqh, hqhy⟩ := htend.label_isY
  obtain ⟨rh, hrh, hrhx⟩ := htend.label_isX
  obtain ⟨zh, hzh, hzhz⟩ := htend.label_isZ
  rw [(by decide : ∀ a : HexDir, a + 3 + 5 = a + 2) d] at hrb hrh
  rw [(by decide : ∀ a : HexDir, a + 3 + 1 = a + 4) d] at hzb hzh
  have hnpar := hst.1
  rw [← hd] at hnpar
  rw [opp_eq_add_three]
  rcases hexDir_cases d e with he | he | he | he | he | he
  · exact absurd (Or.inl he) hnpar
  · -- `e = d + 1`: `h0` is at the deep end; we pass through the cell beyond the partner stick
    subst he
    have hub : nbr (nbr h0 (d + 2)) d = nbr h0 (d + 1) :=
      nbr_nbr_of_vec h0 ((by decide : ∀ a : HexDir, (a + 2).vec + a.vec = (a + 1).vec) d)
    have huh : nbr (nbr h0 (d + 2)) (d + 5) = h0 :=
      nbr_nbr_cancel h0 ((by decide : ∀ a : HexDir, a + 5 = (a + 2).opp) d)
    have hq : T.label (nbr (nbr h0 (d + 2)) d) d.opp = some qb := by
      rw [hub, opp_eq_add_three]; exact hqb
    have hr : T.label (nbr (nbr h0 (d + 2)) (d + 5)) (d + 5).opp = some rh := by
      rw [huh, (by decide : ∀ a : HexDir, (a + 5).opp = a + 2) d]; exact hrh
    have hax : SameAxis (d + 4) (T.dir (nbr h0 (d + 2))) :=
      sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 1) (a + 4)) d)
        (T.sameAxis_dir_of_shallow_sub hv hq hqby hr hrhx)
    have hx : T.label (nbr (nbr h0 (d + 2)) (d + 4 + 1)) (d + 4 + 1).opp = some rh := by
      rw [(by decide : ∀ a : HexDir, a + 4 + 1 = a + 5) d, huh,
        (by decide : ∀ a : HexDir, (a + 5).opp = a + 2) d]
      exact hrh
    have hL : nbr (nbr h0 (d + 2)) (d + 4) = nbr h0 (d + 3) :=
      nbr_nbr_of_vec h0 ((by decide : ∀ a : HexDir, (a + 2).vec + (a + 4).vec = (a + 3).vec) d)
    have hdir := T.dir_nbr_eq_of_isX hv hax hx hrhx
    rw [hL] at hdir
    rw [hdir]
    exact sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 4) (a + 1)) d) hax
  · -- `e = d + 2`: `h0` is at the shallow end
    subst he
    have hlh : nbr (nbr h0 (d + 3)) d = h0 :=
      nbr_nbr_cancel h0 ((by decide : ∀ a : HexDir, a = (a + 3).opp) d)
    have hlb : nbr (nbr h0 (d + 3)) (d + 1) = nbr h0 (d + 2) :=
      nbr_nbr_of_vec h0 ((by decide : ∀ a : HexDir, (a + 3).vec + (a + 1).vec = (a + 2).vec) d)
    have hq : T.label (nbr (nbr h0 (d + 3)) d) d.opp = some qh := by
      rw [hlh, opp_eq_add_three]; exact hqh
    have hne : T.label (nbr h0 (d + 3)) (d + 1) ≠ none := by
      intro hnone
      have h2 := (T.label_eq_none_comm (nbr h0 (d + 3)) (d + 1)).1 hnone
      rw [hlb, (by decide : ∀ a : HexDir, (a + 1).opp = a + 4) d, hzb] at h2
      exact absurd h2 (Option.some_ne_none zb)
    exact T.sameAxis_dir_of_shallow_add hv hq hqhy hne
  · exact absurd (Or.inr he) hnpar
  · -- `e = d + 4`: `h0` is at the shallow end
    subst he
    have hlh : nbr (nbr h0 (d + 3)) d = h0 :=
      nbr_nbr_cancel h0 ((by decide : ∀ a : HexDir, a = (a + 3).opp) d)
    have hlb : nbr (nbr h0 (d + 3)) (d + 5) = nbr h0 (d + 4) :=
      nbr_nbr_of_vec h0 ((by decide : ∀ a : HexDir, (a + 3).vec + (a + 5).vec = (a + 4).vec) d)
    have hq : T.label (nbr (nbr h0 (d + 3)) d) d.opp = some qh := by
      rw [hlh, opp_eq_add_three]; exact hqh
    have hr : T.label (nbr (nbr h0 (d + 3)) (d + 5)) (d + 5).opp = some rb := by
      rw [hlb, (by decide : ∀ a : HexDir, (a + 5).opp = a + 2) d]; exact hrb
    exact sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 1) (a + 4)) d)
      (T.sameAxis_dir_of_shallow_sub hv hq hqhy hr hrbx)
  · -- `e = d + 5`: `h0` is at the deep end
    subst he
    have hub : nbr (nbr h0 (d + 4)) d = nbr h0 (d + 5) :=
      nbr_nbr_of_vec h0 ((by decide : ∀ a : HexDir, (a + 4).vec + a.vec = (a + 5).vec) d)
    have huh : nbr (nbr h0 (d + 4)) (d + 1) = h0 :=
      nbr_nbr_cancel h0 ((by decide : ∀ a : HexDir, a + 1 = (a + 4).opp) d)
    have hq : T.label (nbr (nbr h0 (d + 4)) d) d.opp = some qb := by
      rw [hub, opp_eq_add_three]; exact hqb
    have hne : T.label (nbr h0 (d + 4)) (d + 1) ≠ none := by
      intro hnone
      have h2 := (T.label_eq_none_comm (nbr h0 (d + 4)) (d + 1)).1 hnone
      rw [huh, (by decide : ∀ a : HexDir, (a + 1).opp = a + 4) d, hzh] at h2
      exact absurd h2 (Option.some_ne_none zh)
    have hax : SameAxis (d + 2) (T.dir (nbr h0 (d + 4))) :=
      T.sameAxis_dir_of_shallow_add hv hq hqby hne
    have hz : T.label (nbr (nbr h0 (d + 4)) (d + 2 + 5)) (d + 2 + 5).opp = some zh := by
      rw [(by decide : ∀ a : HexDir, a + 2 + 5 = a + 1) d, huh,
        (by decide : ∀ a : HexDir, (a + 1).opp = a + 4) d]
      exact hzh
    have hL : nbr (nbr h0 (d + 4)) (d + 2) = nbr h0 (d + 3) :=
      nbr_nbr_of_vec h0 ((by decide : ∀ a : HexDir, (a + 4).vec + (a + 2).vec = (a + 3).vec) d)
    have hdir := T.dir_nbr_eq_of_isZ hv hax hz hzhz
    rw [hL] at hdir
    rw [hdir]
    exact sameAxis_trans_axis ((by decide : ∀ a : HexDir, SameAxis (a + 2) (a + 5)) d) hax

/-! ### The two ends of a stick belonging to a stacked pair -/

/-- The last cell of the stick through `c`. -/
def tail (c : Hex) : Hex := T.cellOfStick c (n - 1)

lemma dir_tail (hn : 0 < n) (c : Hex) : T.dir (T.tail c) = T.dir c :=
  T.cellOfStick_dir c (n - 1) (by omega)

lemma idx_tail (hn : 0 < n) (c : Hex) : T.idx (T.tail c) = n := by
  rw [tail, T.cellOfStick_idx c (n - 1) (by omega)]
  omega

lemma tail_mem_stickOf (hn : 0 < n) (c : Hex) : T.tail c ∈ T.stickOf c :=
  (T.mem_stickOf_iff c _).2 ⟨n - 1, by omega, rfl⟩

lemma head_head (c : Hex) : T.head (T.head c) = T.head c := by
  rw [head, T.dir_head c, T.idx_head c]
  norm_num

lemma head_mem_stickOf (c : Hex) : T.head c ∈ T.stickOf c :=
  (T.mem_stickOf_iff_head_eq c _).2 (T.head_head c)

/-- Being stacked only depends on the stick through `c`, not on `c` itself. -/
lemma StackedBy.of_mem_stickOf {c c' x : Hex} {e : HexDir} (hst : T.StackedBy c c' e)
    (hx : x ∈ T.stickOf c) : T.StackedBy x c' e := by
  have hd := T.dir_of_mem_stickOf hx
  have hs := T.stickOf_eq_of_mem hx
  exact ⟨by rw [hd]; exact hst.1, by rw [hd]; exact hst.2.1, by rw [hs]; exact hst.2.2⟩

/-- **Lemma 4, first step.**  If a stick belongs to a stacked pair, then the cells immediately
beyond its two ends are covered by sticks whose axis is the direction in which the pair is
stacked: the sticks at the two ends of a stick in a stacked pair are parallel to the direction
of the stack. -/
theorem sameAxis_dir_nbr_ends_of_stackedBy (hv : T.SatisfiesWeaveRules) (hn : 0 < n) {c c' : Hex}
    {e : HexDir} (hst : T.StackedBy c c' e) :
    SameAxis e (T.dir (nbr (T.tail c) (T.dir c))) ∧
      SameAxis e (T.dir (nbr (T.head c) (T.dir c).opp)) := by
  constructor
  · have h := T.sameAxis_dir_nbr_tail_of_stackedBy hv (T.idx_tail hn c)
      (StackedBy.of_mem_stickOf T hst (T.tail_mem_stickOf hn c))
    rwa [T.dir_tail hn c] at h
  · have h := T.sameAxis_dir_nbr_head_of_stackedBy hv (T.idx_head c)
      (StackedBy.of_mem_stickOf T hst (T.head_mem_stickOf c))
    rwa [T.dir_head c] at h

/-! ### Left-leaning and right-leaning stacked pairs -/

/-- Swapping the two sticks of a stacked pair. -/
lemma StackedBy.symm {c c' : Hex} {e : HexDir} (hst : T.StackedBy c c' e) :
    T.StackedBy c' c e.opp := by
  have himg := T.stickOf_eq_image_of_stackedBy hst
  refine ⟨?_, hst.2.1.symm, ?_⟩
  · exact (by decide : ∀ a b e : HexDir, ¬ SameAxis a e → SameAxis a b → ¬ SameAxis b e.opp)
      (T.dir c) (T.dir c') e hst.1 hst.2.1
  · intro x hx
    rw [himg] at hx
    simp only [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rwa [nbr_opp_nbr]

/-- A stacked pair *leans left*: the partner stick sits on the side of the stick through `c`
towards `T.dir c + 2` (equivalently, towards `T.dir c + 5`).  For a horizontal stick, with
`HexDir.NE` pointing up and to the right, this says that the upper stick of the pair is shifted
to the left; the condition is invariant under rotating the whole picture. -/
def LeansLeft (c c' : Hex) : Prop :=
  ∃ e, T.StackedBy c c' e ∧ (e = T.dir c + 2 ∨ e = T.dir c + 5)

/-- A stacked pair *leans right*: the partner stick sits on the side of the stick through `c`
towards `T.dir c + 1` (equivalently, towards `T.dir c + 4`).  For a horizontal stick this says
that the upper stick of the pair is shifted to the right. -/
def LeansRight (c c' : Hex) : Prop :=
  ∃ e, T.StackedBy c c' e ∧ (e = T.dir c + 1 ∨ e = T.dir c + 4)

/-- With `HexDir.NE` pointing up and to the right, a stacked pair of horizontal sticks leans
left exactly when the partner stick is the given one shifted up and to the left (or, what is the
same pair seen the other way round, down and to the right). -/
lemma leansLeft_horizontal {c c' : Hex} (hdir : T.dir c = HexDir.E) :
    T.LeansLeft c c' ↔ ∃ e, T.StackedBy c c' e ∧ (e = HexDir.NW ∨ e = HexDir.SE) := by
  rw [LeansLeft, hdir, (by decide : HexDir.E + 2 = HexDir.NW),
    (by decide : HexDir.E + 5 = HexDir.SE)]

/-- Every stacked pair leans either left or right. -/
theorem leansLeft_or_leansRight {c c' : Hex} (h : T.IsStackedPair c c') :
    T.LeansLeft c c' ∨ T.LeansRight c c' := by
  obtain ⟨e, hst⟩ := h
  rcases hexDir_cases (T.dir c) e with he | he | he | he | he | he
  · exact absurd (Or.inl he) hst.1
  · exact Or.inr ⟨e, hst, Or.inl he⟩
  · exact Or.inl ⟨e, hst, Or.inl he⟩
  · exact absurd (Or.inr he) hst.1
  · exact Or.inr ⟨e, hst, Or.inr he⟩
  · exact Or.inl ⟨e, hst, Or.inr he⟩

/-- The direction in which a pair is stacked is unique. -/
theorem stackedBy_unique (hn : 0 < n) {c c' : Hex} {e e' : HexDir} (h : T.StackedBy c c' e)
    (h' : T.StackedBy c c' e') : e = e' := by
  have hsum : ∀ f : HexDir, ∑ x ∈ (T.stickOf c).image (fun x => nbr x f), x
      = (∑ x ∈ T.stickOf c, x) + n • f.vec := by
    intro f
    rw [Finset.sum_image (fun a _ b _ hab => by simpa [nbr] using hab)]
    simp [nbr, Finset.sum_add_distrib, T.card_stickOf]
  have himg : (T.stickOf c).image (fun x => nbr x e)
      = (T.stickOf c).image (fun x => nbr x e') := by
    rw [← T.stickOf_eq_image_of_stackedBy h, ← T.stickOf_eq_image_of_stackedBy h']
  have h2 : (∑ x ∈ T.stickOf c, x) + n • e.vec = (∑ x ∈ T.stickOf c, x) + n • e'.vec := by
    rw [← hsum e, ← hsum e', himg]
  exact HexDir.vec_injective (smul_right_injective (ℤ × ℤ) hn.ne' (add_left_cancel h2))

/-- A stacked pair cannot lean both ways. -/
theorem not_leansLeft_and_leansRight (hn : 0 < n) {c c' : Hex} :
    ¬ (T.LeansLeft c c' ∧ T.LeansRight c c') := by
  rintro ⟨⟨e, hst, hl⟩, ⟨f, hst', hr⟩⟩
  have hef : e = f := T.stackedBy_unique hn hst hst'
  subst hef
  exact (by decide : ∀ a e : HexDir, (e = a + 2 ∨ e = a + 5) → (e = a + 1 ∨ e = a + 4) → False)
    (T.dir c) e hl hr

/-- Leaning left is a property of the pair: it does not depend on which of the two sticks of the
pair is taken first. -/
theorem leansLeft_symm {c c' : Hex} (h : T.LeansLeft c c') : T.LeansLeft c' c := by
  obtain ⟨e, hst, hl⟩ := h
  exact ⟨e.opp, StackedBy.symm T hst,
    (by decide : ∀ a b e : HexDir, SameAxis a b → (e = a + 2 ∨ e = a + 5) →
      (e.opp = b + 2 ∨ e.opp = b + 5)) (T.dir c) (T.dir c') e hst.2.1 hl⟩

/-- Leaning right is likewise a property of the pair. -/
theorem leansRight_symm {c c' : Hex} (h : T.LeansRight c c') : T.LeansRight c' c := by
  obtain ⟨e, hst, hl⟩ := h
  exact ⟨e.opp, StackedBy.symm T hst,
    (by decide : ∀ a b e : HexDir, SameAxis a b → (e = a + 1 ∨ e = a + 4) →
      (e.opp = b + 1 ∨ e.opp = b + 4)) (T.dir c) (T.dir c') e hst.2.1 hl⟩

end StickTiling

end StickPolyhex
