import Tiling.Proofs.LeftLeaning

/-!
# The weave pattern

This file formalises the *weave pattern* of the paper (the picture that the matching rules are
designed to force) and states Lemma 4: every valid tiling forms a weave pattern.

## Orientation

The paper says that a tiling *forms a weave pattern* if **it can be oriented** so that a list of
conditions holds.  Choosing the orientation amounts to choosing a direction `u : HexDir`, which
plays the role of the direction `W` of the reference picture of the prototile: a stick is

* *horizontal with its arrow pointing down* when its direction is `u`,
* *horizontal* when its direction is `u` or `u + 3`,
* *slanting left* when its direction is `u + 2` or `u + 5` (`StickTiling.SlantsLeft`),
* *slanting right* when its direction is `u + 1` or `u + 4` (`StickTiling.SlantsRight`).

Indeed, with `HexDir.NE` drawn up and to the right and `u = HexDir.W`, the direction of
increasing index of a horizontal stick with the arrow pointing down is `W`, the left-slanting
axis is `{NW, SE}` and the right-slanting axis is `{NE, SW}`.

## The conditions

`StickTiling.IsWeavePattern T u` collects the nine bullet points of the paper, in the same order;
see the docstrings of its fields.  `StickTiling.FormsWeavePattern` says that some orientation
works; Lemma 4 of the paper, `StickTiling.formsWeavePattern_of_satisfiesWeaveRules`, is proved in
`Tiling/Proofs/Lemma4.lean`.

## State of the proof of Lemma 4

The following ingredients of the proof are established here (on top of the results of
`Tiling/Proofs/LeftLeaning.lean`, which produce a left-leaning stack and show that it has
height exactly `n`).  Throughout, `u` denotes the direction of the sticks of a fixed
left-leaning stack.

* `dir_eq_of_sameStack_of_isLeftLeaningStack`: all the sticks of a left-leaning stack point the
  same way, so a left-leaning stack really is a stack of `n` parallel horizontal sticks.
* `dir_beyond_ends_of_isLeftLeaningStack`: the cells just beyond the two ends of each stick of
  the stack are covered by left-slanting sticks, of direction `u + 5` beyond the far ends and
  `u + 2` beyond the near ends: the two sticks flanking the stack carry their arrows away from
  it, as in the weave pattern.
* `exists_sameStack_frontCell_eq`: each of the two flanking sticks meets *all* `n` sticks of the
  stack, so the stack and its flanking sticks have the same extent.
* `dir_backCorner_beyond_tail` and `dir_frontCorner_beyond_head`: the cells `A` of Figure 11,
  diagonally beyond the ends of the sticks of the stack, are again covered by horizontal sticks
  of direction `u`, which meet some but not all of the concave corners of the stack.  This is
  the case analysis of Figure 12 of the paper.
* `dir_eq_of_stackedBy_back` and `no_back_to_back_of_satisfiesWeaveRules`: two sticks stacked on the back
  side of one of them are parallel, i.e. two sticks of a vertical stack are never stacked back
  to back.  This is the ninth condition of the weave pattern, and it holds in every valid
  tiling.

The propagation step of Figures 13 to 15 is carried out in `Tiling/Proofs/WeaveUp.lean` and
`Tiling/Proofs/WeaveDown.lean`:

* `dir_eastCell_head_of_backCorner` and `isLeftLeaningStack_backCorner`: the horizontal stick
  filling the space `A` is itself part of a left-leaning stack;
* `exists_backCorner_not_sameStack` and `exists_stackAbove_isLeftLeaningStack`: that stack is a
  *different* stack, lying above the given one, so every left-leaning stack has a left-leaning
  stack above it;
* `dir_westCell_tail_of_frontCorner`, `isLeftLeaningStack_frontCorner`,
  `exists_frontCorner_not_sameStack` and `exists_stackBelow_isLeftLeaningStack`: the mirror
  statements on the front side, so every left-leaning stack also has a left-leaning stack below
  it;
* `exists_weave_neighbours_of_satisfiesWeaveRules`: the resulting block of the weave pattern, a left-leaning
  stack of `n` horizontal sticks with a left-leaning stack of `n` horizontal sticks of the same
  direction above it and another one below it.

The second stack on each side (the space `B` of Figures 16 and 17), the fact that there are no
further neighbouring horizontal stacks, and the induction of Figure 18 covering the plane by a
grid of horizontal stacks are carried out in the later files `Tiling/Proofs/StackTop.lean`,
`Tiling/Proofs/StackBottom.lean`, `Tiling/Proofs/StackNeighbours.lean`,
`Tiling/Proofs/StackFour.lean`, `Tiling/Proofs/Coverage.lean`,
`Tiling/Proofs/HoleStacks.lean`, `Tiling/Proofs/HoleEnds.lean`,
`Tiling/Proofs/StepStack.lean`, `Tiling/Proofs/StepHole.lean` and
`Tiling/Proofs/GridStructure.lean`, and the whole lemma is assembled in
`Tiling/Proofs/Lemma4.lean`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Orientation classes of sticks -/

/-- The stick through `c` *slants left* for the orientation `u`: its axis is `{u + 2, u + 5}`. -/
def SlantsLeft (u : HexDir) (c : Hex) : Prop := T.dir c = u + 2 ∨ T.dir c = u + 5

/-- The stick through `c` *slants right* for the orientation `u`: its axis is `{u + 1, u + 4}`. -/
def SlantsRight (u : HexDir) (c : Hex) : Prop := T.dir c = u + 1 ∨ T.dir c = u + 4

/-- The stick through `c` is *horizontal* for the orientation `u`: its axis is `{u, u + 3}`. -/
def IsHorizontal (u : HexDir) (c : Hex) : Prop := T.dir c = u ∨ T.dir c = u + 3

/-- A stack is *right-leaning* when it contains a right-leaning stacked pair.  (By
`leansRight_iff_of_sameStack` all its stacked pairs then lean right.) -/
def IsRightLeaningStack (c : Hex) : Prop := ∃ a b, T.SameStack c a ∧ T.LeansRight a b

/-! ### Adjacency of stacks -/

/-- Two stacks are *adjacent* when they are distinct and some cell of one is a neighbour of some
cell of the other. -/
def StackAdjacent (c c' : Hex) : Prop :=
  ¬ T.SameStack c c' ∧ ∃ x e, T.SameStack c x ∧ T.SameStack c' (nbr x e)

/-- The stack through `c'` lies *above* the stack through `c` (for the orientation `u`): the two
stacks are distinct and some cell of the stack of `c'` is a neighbour, in one of the two upward
directions `u + 4`, `u + 5`, of a cell of the stack of `c`. -/
def StackAbove (u : HexDir) (c c' : Hex) : Prop :=
  ¬ T.SameStack c c' ∧ ∃ x, T.SameStack c x ∧
    (T.SameStack c' (nbr x (u + 4)) ∨ T.SameStack c' (nbr x (u + 5)))

/-- The stack through `c'` lies *below* the stack through `c`: the mirror image of
`StickTiling.StackAbove`, using the two downward directions `u + 1`, `u + 2`. -/
def StackBelow (u : HexDir) (c c' : Hex) : Prop :=
  ¬ T.SameStack c c' ∧ ∃ x, T.SameStack c x ∧
    (T.SameStack c' (nbr x (u + 1)) ∨ T.SameStack c' (nbr x (u + 2)))

/-- Lying above and lying below are opposite relations. -/
lemma stackBelow_of_stackAbove {u : HexDir} {c c' : Hex} (h : T.StackAbove u c c') :
    T.StackBelow u c' c := by
  obtain ⟨hne, x, hx, hx'⟩ := h
  refine ⟨fun h => hne (SameStack.symm T h), ?_⟩
  rcases hx' with h4 | h5
  · exact ⟨nbr x (u + 4), h4, Or.inl (by rw [nbr_nbr_cancel x (opp_add_four u).symm]; exact hx)⟩
  · exact ⟨nbr x (u + 5), h5, Or.inr (by rw [nbr_nbr_cancel x (opp_add_five u).symm]; exact hx)⟩

/-- Lying below and lying above are opposite relations. -/
lemma stackAbove_of_stackBelow {u : HexDir} {c c' : Hex} (h : T.StackBelow u c c') :
    T.StackAbove u c' c := by
  obtain ⟨hne, x, hx, hx'⟩ := h
  refine ⟨fun h => hne (SameStack.symm T h), ?_⟩
  rcases hx' with h1 | h2
  · exact ⟨nbr x (u + 1), h1, Or.inl (by rw [nbr_nbr_cancel x (opp_add_one u).symm]; exact hx)⟩
  · exact ⟨nbr x (u + 2), h2, Or.inr (by rw [nbr_nbr_cancel x (opp_add_two u).symm]; exact hx)⟩

/-! ### The weave pattern -/

/-- **The weave pattern.**  A valid tiling *forms a weave pattern* when it can be oriented, i.e.
when there is a direction `u` playing the role of the direction of a horizontal stick with its
arrow pointing down, so that the nine conditions of the paper hold. -/
structure IsWeavePattern (u : HexDir) : Prop where
  /-- Every stick is horizontal or slants left; moreover every horizontal stick has its arrow
  pointing down, i.e. its direction is exactly `u` (this is the paper's first and fifth
  bullet points). -/
  horizontal_or_slantsLeft : ∀ c, T.dir c = u ∨ T.SlantsLeft u c
  /-- There is a horizontal stick. -/
  exists_horizontal : ∃ c, T.dir c = u
  /-- All the horizontal sticks lie in left-leaning stacks (the *horizontal stacks*). -/
  horizontal_leftLeaning : ∀ c, T.dir c = u → T.IsLeftLeaningStack c
  /-- All the left-slanting sticks lie in right-leaning stacks (the *vertical stacks*). -/
  slantsLeft_rightLeaning : ∀ c, T.SlantsLeft u c → T.IsRightLeaningStack c
  /-- All the horizontal stacks have height `n`. -/
  horizontal_height : ∀ c, T.dir c = u → T.stackHeight c = n
  /-- Each horizontal stack has exactly two horizontal stacks above it and exactly two below it,
  so that the adjacency graph of the horizontal stacks is an infinite diagonal grid.  As in the
  paper, the uniqueness clauses speak of the *horizontal* stacks lying above and below `c`; the
  left-slanting sticks flanking `c` also lie above and below it, but they are vertical stacks. -/
  two_above_two_below : ∀ c, T.dir c = u →
    (∃ a₁ a₂, T.dir a₁ = u ∧ T.dir a₂ = u ∧ ¬ T.SameStack a₁ a₂ ∧
        T.StackAbove u c a₁ ∧ T.StackAbove u c a₂ ∧
        ∀ a, T.dir a = u → T.StackAbove u c a → T.SameStack a a₁ ∨ T.SameStack a a₂) ∧
      (∃ b₁ b₂, T.dir b₁ = u ∧ T.dir b₂ = u ∧ ¬ T.SameStack b₁ b₂ ∧
        T.StackBelow u c b₁ ∧ T.StackBelow u c b₂ ∧
        ∀ b, T.dir b = u → T.StackBelow u c b → T.SameStack b b₁ ∨ T.SameStack b b₂)
  /-- Adjacent horizontal stacks overlap by at least one concave corner: a cell `x` of the lower
  stack which is not the last cell of its stick has its upper-left neighbour in the upper
  stack, so that the upper stack fills the corner between `x` and the next cell of its stick. -/
  overlap : ∀ c c', T.dir c = u → T.dir c' = u → T.StackAbove u c c' →
    ∃ x, T.SameStack c x ∧ T.idx x < n ∧ T.SameStack c' (nbr x (u + 5))
  /-- The four horizontal stacks making up a cell of the grid enclose a vertical stack, i.e. a
  right-leaning stack of left-slanting sticks, containing at least two sticks and adjacent to
  each of the four. -/
  grid_cell : ∀ c a₁ a₂, T.dir c = u → T.dir a₁ = u → T.dir a₂ = u →
    T.StackAbove u c a₁ → T.StackAbove u c a₂ → ¬ T.SameStack a₁ a₂ →
    ∃ a₃ v, T.dir a₃ = u ∧ T.StackAbove u a₁ a₃ ∧ T.StackAbove u a₂ a₃ ∧
      T.SlantsLeft u v ∧ 2 ≤ T.stackHeight v ∧ T.StackAdjacent v c ∧ T.StackAdjacent v a₁ ∧
      T.StackAdjacent v a₂ ∧ T.StackAdjacent v a₃
  /-- Every vertical stack splits into a left part, whose sticks have their arrows pointing
  right, and a right part, whose sticks have their arrows pointing left: no two sticks of a
  vertical stack are stacked back to back. -/
  no_back_to_back : ∀ v v', T.dir v = u + 5 → T.StackedBy v v' (u + 3) → T.dir v' ≠ u + 2

/-- A tiling *forms a weave pattern* when it can be oriented so that the conditions of
`StickTiling.IsWeavePattern` hold. -/
def FormsWeavePattern : Prop := ∃ u, T.IsWeavePattern u

/-! ### All sticks of a left-leaning stack are parallel -/

/-- In a left-leaning stack, all the sticks have the same direction (and not merely the same
axis): rules 6 and 8 make the arrows of two stacked sticks point the same way. -/
theorem dir_eq_of_sameStack_of_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex}
    (hL : T.IsLeftLeaningStack c) (h : T.SameStack c x) : T.dir x = T.dir c := by
  obtain ⟨a, b, hca, hab⟩ := hL
  obtain ⟨e, hste, hle⟩ := hab
  induction h with
  | refl => rfl
  | @tail y x hcy hyx ih =>
    rcases hyx with hstick | hpair
    · have hmem : x ∈ T.stickOf y := by rw [hstick]; exact T.self_mem_stickOf x
      rw [T.dir_of_mem_stickOf hmem]
      exact ih
    · have hsay : T.SameStack a y := SameStack.trans T (SameStack.symm T hca) hcy
      have hll : T.LeansLeft y x :=
        (T.leansLeft_iff_of_sameStack hv (by omega) hsay ⟨e, hste⟩ hpair).1 ⟨e, hste, hle⟩
      rw [T.dir_eq_of_leansLeft hv hn hll]
      exact ih

/-! ### The sticks lying beyond the two ends of a stack -/

/-- Mirror image of `dir_frontCell_of_stackedBy_five`: the stick lying just beyond the near end
(the head) of a stick belonging to a left-leaning pair stacked towards `dir s + 2` points in the
direction `dir s + 2`, so that the ends of the sticks of the stack fill *its* back corners. -/
lemma dir_backCell_of_stackedBy_two (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {s s' : Hex}
    (hst : T.StackedBy s s' (T.dir s + 2)) :
    T.dir (nbr (T.head s) (T.dir s).opp) = T.dir s + 2 := by
  set h := T.head s with hh
  have hdh : T.dir h = T.dir s := T.dir_head s
  have hih : T.idx h = 1 := T.idx_head s
  have hsth : T.StackedBy h s' (T.dir s + 2) :=
    StackedBy.of_mem_stickOf T hst (T.head_mem_stickOf s)
  have hax := T.sameAxis_dir_nbr_head_of_stackedBy hv hih hsth
  rw [hdh] at hax
  rcases hax with hw | hw
  · exact hw
  rw [opp_add_two] at hw
  exfalso
  set z := nbr h (T.dir s).opp with hz
  have hzh : nbr z (T.dir s) = h := by
    rw [hz, opp_eq_add_three]
    exact nbr_nbr_cancel h (opp_add_three (T.dir s)).symm
  have hfive : T.dir s + 5 + 1 = T.dir s := (by decide : ∀ a : HexDir, a + 5 + 1 = a) _
  by_cases hidx : T.idx z < n
  · have hP := T.not_sameAxis_dir_frontCorner hv hn (p := z) hidx
    rw [hw, hfive, hzh, hdh] at hP
    exact hP (sameAxis_self _)
  · have hidxn : T.idx z = n := by have := T.idx_le z; omega
    have h1 : 1 < T.idx z := by omega
    have hdz' : T.dir (nbr z (T.dir z).opp) = T.dir z := T.pred_dir z h1
    have hiz' : T.idx (nbr z (T.dir z).opp) = T.idx z - 1 := T.pred_idx z h1
    have hP := T.not_sameAxis_dir_frontCorner hv hn (p := nbr z (T.dir z).opp) (by omega)
    rw [hdz', hw, hfive, opp_add_five, nbr_comm, hzh] at hP
    have hmem : nbr h (T.dir s + 2) ∈ T.stickOf s' := hsth.2.2 h (T.self_mem_stickOf h)
    exact hP (by rw [T.dir_of_mem_stickOf hmem]; exact hst.2.1)

/-- The cells just beyond the sticks of one stack, taken in a fixed direction `d` parallel to
the sticks, all lie on a single stick.  This is
`sameAxis_and_frontCell_mem_of_sameStack` with an arbitrary direction of the common axis in
place of the direction of the sticks themselves. -/
lemma frontCell_mem_of_sameStack (hv : T.SatisfiesWeaveRules) (hn : 0 < n) {d : HexDir} {c x : Hex}
    (hax0 : SameAxis d (T.dir c)) (h : T.SameStack c x) :
    SameAxis d (T.dir x) ∧ T.frontCell d x ∈ T.stickOf (T.frontCell d c) := by
  induction h with
  | refl => exact ⟨hax0, T.self_mem_stickOf _⟩
  | @tail b x hcb hbx ih =>
    obtain ⟨hax, hmem⟩ := ih
    rcases hbx with hstick | ⟨e, hst⟩
    · have hxb : x ∈ T.stickOf b := by rw [hstick]; exact T.self_mem_stickOf x
      have hhead : T.head x = T.head b := (T.mem_stickOf_iff_head_eq b x).1 hxb
      have hdir : T.dir x = T.dir b := T.dir_of_mem_stickOf hxb
      exact ⟨by rw [hdir]; exact hax, by rw [T.frontCell_congr d hhead]; exact hmem⟩
    · have haxx : SameAxis d (T.dir x) := sameAxis_trans_axis hax.symm hst.2.1
      refine ⟨haxx, ?_⟩
      have hstep : T.frontCell d x = nbr (T.frontCell d b) e := T.frontCell_of_stackedBy hn hax hst
      have h1 : SameAxis e (T.dir (T.frontCell d b)) :=
        T.sameAxis_dir_frontCell_of_stackedBy hv hn hax hst
      have h2 : SameAxis e (T.dir (T.frontCell d x)) := by
        have := T.sameAxis_dir_frontCell_of_stackedBy hv hn haxx (StackedBy.symm T hst)
        exact (by decide : ∀ u v : HexDir, SameAxis u.opp v → SameAxis u v) e _ this
      have hin : nbr (T.frontCell d b) e ∈ T.stickOf (T.frontCell d b) :=
        T.mem_stickOf_nbr_of_sameAxis hv h1 (by rw [← hstep]; exact h2)
      rw [hstep]
      rw [T.stickOf_eq_of_mem hmem] at hin
      exact hin

/-- **The two sticks flanking a left-leaning stack.**  For every stick of a left-leaning stack,
the cell just beyond its far end (its tail) is covered by a stick of direction `dir c + 5`, and
the cell just beyond its near end (its head) by a stick of direction `dir c + 2`.  Both are
left-slanting sticks for the orientation `u = dir c`, and their arrows point away from the
stack. -/
theorem dir_beyond_ends_of_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex}
    (hL : T.IsLeftLeaningStack c) (h : T.SameStack c x) :
    T.dir (nbr (T.tail x) (T.dir c)) = T.dir c + 5 ∧
      T.dir (nbr (T.head x) (T.dir c).opp) = T.dir c + 2 := by
  have h0n : 0 < n := by omega
  -- a stacked pair of the stack, normalised in both ways
  obtain ⟨a, b, hca, hab⟩ := hL
  have hda : T.dir a = T.dir c :=
    T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn ⟨a, b, hca, hab⟩ hca
  have hdb : T.dir b = T.dir a := T.dir_eq_of_leansLeft hv hn hab
  obtain ⟨e, hste, he⟩ := hab
  -- the pair stacked towards `dir + 5`, and the pair stacked towards `dir + 2`
  obtain ⟨p, p', hcp, hstp⟩ : ∃ p p', T.SameStack c p ∧ T.StackedBy p p' (T.dir p + 5) := by
    rcases he with he | he
    · refine ⟨b, a, SameStack.trans T hca (T.sameStack_of_isStackedPair ⟨e, hste⟩), ?_⟩
      have hsym := StackedBy.symm T hste
      rw [he, opp_add_two, ← hdb] at hsym
      exact hsym
    · exact ⟨a, b, hca, by rw [← he]; exact hste⟩
  obtain ⟨q, q', hcq, hstq⟩ : ∃ q q', T.SameStack c q ∧ T.StackedBy q q' (T.dir q + 2) := by
    rcases he with he | he
    · exact ⟨a, b, hca, by rw [← he]; exact hste⟩
    · refine ⟨b, a, SameStack.trans T hca (T.sameStack_of_isStackedPair ⟨e, hste⟩), ?_⟩
      have hsym := StackedBy.symm T hste
      rw [he, opp_add_five, ← hdb] at hsym
      exact hsym
  have hdp : T.dir p = T.dir c :=
    T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn ⟨a, b, hca, ⟨e, hste, he⟩⟩ hcp
  have hdq : T.dir q = T.dir c :=
    T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn ⟨a, b, hca, ⟨e, hste, he⟩⟩ hcq
  have hdx : T.dir x = T.dir c :=
    T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn ⟨a, b, hca, ⟨e, hste, he⟩⟩ h
  constructor
  · -- beyond the tail
    have hkey : T.dir (nbr (T.tail p) (T.dir p)) = T.dir p + 5 :=
      T.dir_frontCell_of_stackedBy_five hv hn hstp
    rw [hdp] at hkey
    have hfp : T.frontCell (T.dir c) p = nbr (T.tail p) (T.dir c) := by
      rw [frontCell, endCell, if_pos hdp]
    have hfx : T.frontCell (T.dir c) x = nbr (T.tail x) (T.dir c) := by
      rw [frontCell, endCell, if_pos hdx]
    have hmem := (T.frontCell_mem_of_sameStack hv h0n (d := T.dir c)
      (Or.inl hdp) (SameStack.trans T (SameStack.symm T hcp) h)).2
    have hdirs := T.dir_of_mem_stickOf hmem
    rw [hfx, hfp] at hdirs
    rw [hdirs, hkey]
  · -- beyond the head
    have hkey : T.dir (nbr (T.head q) (T.dir q).opp) = T.dir q + 2 :=
      T.dir_backCell_of_stackedBy_two hv hn hstq
    rw [hdq] at hkey
    have hne : T.dir q ≠ (T.dir c).opp := by
      rw [hdq]; exact (by decide : ∀ a : HexDir, a ≠ a.opp) _
    have hnex : T.dir x ≠ (T.dir c).opp := by
      rw [hdx]; exact (by decide : ∀ a : HexDir, a ≠ a.opp) _
    have hfq : T.frontCell (T.dir c).opp q = nbr (T.head q) (T.dir c).opp := by
      rw [frontCell, endCell, if_neg hne]
    have hfx : T.frontCell (T.dir c).opp x = nbr (T.head x) (T.dir c).opp := by
      rw [frontCell, endCell, if_neg hnex]
    have hax0 : SameAxis (T.dir c).opp (T.dir q) :=
      Or.inr (by rw [hdq, HexDir.opp_opp])
    have hmem := (T.frontCell_mem_of_sameStack hv h0n (d := (T.dir c).opp)
      hax0 (SameStack.trans T (SameStack.symm T hcq) h)).2
    have hdirs := T.dir_of_mem_stickOf hmem
    rw [hfx, hfq] at hdirs
    rw [hdirs, hkey]

/-- A left-leaning stack has exactly `n` sticks, counted through their heads. -/
lemma stackHeads_ncard_of_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex}
    (hL : T.IsLeftLeaningStack c) : (T.stackHeads c).ncard = n := by
  have hinj : Set.InjOn (fun y => T.stickOf y) (T.stackHeads c) := by
    rintro y1 ⟨x1, _, rfl⟩ y2 ⟨x2, _, rfl⟩ hs
    simp only at hs
    have hmem : T.head x1 ∈ T.stickOf (T.head x2) := by
      rw [← hs]; exact T.self_mem_stickOf _
    have := (T.mem_stickOf_iff_head_eq (T.head x2) (T.head x1)).1 hmem
    rwa [T.head_head, T.head_head] at this
  have himg := Set.InjOn.ncard_image hinj
  rw [← T.stack_eq_image_stackHeads c] at himg
  have hheight := T.stackHeight_eq_of_isLeftLeaningStack hv hn hL
  rw [stackHeight] at hheight
  omega

/-- The cells beyond the sticks of a stack, in a fixed direction `d` of their common axis, are
pairwise distinct. -/
lemma frontCell_injOn_stackHeads' (hn : 0 < n) (d : HexDir) (c : Hex) :
    Set.InjOn (T.frontCell d) (T.stackHeads c) := by
  rintro y1 ⟨x1, _, rfl⟩ y2 ⟨x2, _, rfl⟩ hfc
  have hst := T.stickOf_eq_of_frontCell_eq hn hfc
  have hmem : T.head x1 ∈ T.stickOf (T.head x2) := by
    rw [← hst]; exact T.self_mem_stickOf _
  have := (T.mem_stickOf_iff_head_eq (T.head x2) (T.head x1)).1 hmem
  rwa [T.head_head, T.head_head] at this

/-- **A left-leaning stack meets each of its two flanking sticks in all of their cells.**  Every
cell of the stick lying beyond the sticks of a left-leaning stack, in a direction `d` of their
common axis, lies beyond one of the sticks of the stack: the stack and the stick flanking it
have the same extent. -/
theorem exists_sameStack_frontCell_eq (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c y : Hex} {d : HexDir}
    (hL : T.IsLeftLeaningStack c) (hax : SameAxis d (T.dir c))
    (hy : y ∈ T.stickOf (T.frontCell d c)) :
    ∃ x, T.SameStack c x ∧ T.frontCell d x = y := by
  have h0n : 0 < n := by omega
  have hmaps : ∀ z ∈ T.stackHeads c, T.frontCell d z ∈ (T.stickOf (T.frontCell d c) : Set Hex) := by
    rintro z ⟨x, hx, rfl⟩
    rw [T.frontCell_head]
    exact_mod_cast (T.frontCell_mem_of_sameStack hv h0n hax hx).2
  have hsub : (T.frontCell d) '' (T.stackHeads c) ⊆ ↑(T.stickOf (T.frontCell d c)) :=
    Set.image_subset_iff.2 hmaps
  have hcard : ((T.frontCell d) '' (T.stackHeads c)).ncard = n := by
    rw [Set.InjOn.ncard_image (T.frontCell_injOn_stackHeads' h0n d c)]
    exact T.stackHeads_ncard_of_isLeftLeaningStack hv hn hL
  have heq : (T.frontCell d) '' (T.stackHeads c) = ↑(T.stickOf (T.frontCell d c)) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [hcard, Set.ncard_coe_finset, T.card_stickOf]
  have hy' : y ∈ (T.frontCell d) '' (T.stackHeads c) := by
    rw [heq]
    exact_mod_cast hy
  obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := hy'
  exact ⟨x, hx, by rwa [T.frontCell_head] at hz⟩

/-- Every cell of the stick lying beyond the tails of a left-leaning stack is the cell beyond
the tail of one of the sticks of the stack. -/
theorem exists_sameStack_of_mem_flankingStick (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c y : Hex}
    (hL : T.IsLeftLeaningStack c) (hy : y ∈ T.stickOf (nbr (T.tail c) (T.dir c))) :
    ∃ x, T.SameStack c x ∧ nbr (T.tail x) (T.dir c) = y := by
  have hfc : T.frontCell (T.dir c) c = nbr (T.tail c) (T.dir c) := by
    rw [frontCell, endCell, if_pos rfl]
  obtain ⟨x, hx, hxy⟩ := T.exists_sameStack_frontCell_eq hv hn hL (sameAxis_self _)
    (by rw [hfc]; exact hy)
  have hdx : T.dir x = T.dir c := T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx
  refine ⟨x, hx, ?_⟩
  rwa [frontCell, endCell, if_pos hdx] at hxy

/-! ### The stick above the far end of a left-leaning stack -/

/-- **The space `A` of the paper (Figure 11) is filled by a horizontal stick.**  Let `x` be a
stick of a left-leaning stack of direction `u`.  The cell diagonally beyond the far end of `x`,
on its back side, is covered by a stick of direction `u` again -- a horizontal stick whose arrow
points the same way.  Moreover that cell is either the far end of the next stick up the stack,
or an interior cell of a new horizontal stick, which therefore meets some but not all of the
concave corners on the back side of `x`.

The proof is the case analysis of Figure 12: the cell in question faces two `x₂` labels, one
presented by the end of `x` and one by the end of the stick flanking the stack, and the rules
forbidding `x` labels to meet `x`, `y`, `z` and `a` labels leave only the stated possibility. -/
theorem dir_backCorner_beyond_tail (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x) :
    T.dir (nbr (T.tail x) (u + 5)) = u ∧
      ((T.idx (nbr (T.tail x) (u + 5)) = n ∧ T.SameStack c (nbr (T.tail x) (u + 5))) ∨
        (1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n)) := by
  have h0n : 0 < n := by omega
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx, hu]
  have hdt : T.dir (T.tail x) = u := by rw [T.dir_tail h0n x, hdx]
  have hit : T.idx (T.tail x) = n := T.idx_tail h0n x
  -- `Wc` is the cell of the flanking stick lying beyond the tail of `x`
  set Wc := nbr (T.tail x) u with hWc
  set A := nbr (T.tail x) (u + 5) with hA
  have hdW : T.dir Wc = u + 5 := by
    have := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL hx).1
    rw [hu] at this
    exact this
  have hWA : nbr Wc (u + 4) = A := by
    rw [hWc, hA]
    exact nbr_nbr_of_vec (T.tail x) (vec_zero_four u)
  by_cases hWidx : T.idx Wc = n
  · -- the flanking stick ends beside the tail of `x`: the label analysis of Figure 12
    have hx2t : T.label (T.tail x) (u + 5) = some .x2 := by
      rw [show u + 5 = T.dir (T.tail x) + 5 by rw [hdt], T.label_dir_add_five, if_pos hit]
    have hx2W : T.label Wc (u + 4) = some .x2 := by
      rw [T.label_shift5 (u := u) (k := 5) (j := 4) hdW (by decide : (4 : HexDir) = 5 + 5),
        if_pos hWidx]
    have hface2 : ∀ Q, T.label A (u + 2) = some Q → ¬ Forbidden n .x2 Q := fun Q hQ hf =>
      T.clash hv hx2t (by rw [opp_add_five]; exact hQ) hf
    have hnone2 : T.label A (u + 2) ≠ none := fun h =>
      T.no_none hx2t (by rw [opp_add_five]; exact h)
    have hface1 : ∀ Q, T.label A (u + 1) = some Q → ¬ Forbidden n .x2 Q := fun Q hQ hf =>
      T.clash hv hx2W (by rw [hWA, opp_add_four]; exact hQ) hf
    have hnone1 : T.label A (u + 1) ≠ none := fun h =>
      T.no_none hx2W (by rw [hWA, opp_add_four]; exact h)
    have hposA := T.idx_pos A
    have hleA := T.idx_le A
    rcases hexDir_cases u (T.dir A) with hk | hk | hk | hk | hk | hk
    · have hd0 : T.dir A = u + 0 := by rw [hk, add_zero]
      refine ⟨hk, Or.inr ⟨?_, ?_⟩⟩
      · by_contra hi
        have hi1 : T.idx A = 1 := by omega
        exact hface2 .x1
          (by rw [T.label_shift2 hd0 (by decide : (2 : HexDir) = 0 + 2), if_pos hi1])
          (Or.inl (ForbiddenCore.rule2x (Or.inr rfl) (Or.inl rfl)))
      · by_contra hi
        have hin : T.idx A = n := by omega
        exact hface1 .z2
          (by rw [T.label_shift1 hd0 (by decide : (1 : HexDir) = 0 + 1), if_pos hin])
          (forbidden_of_isX_isZ (Or.inr rfl) (Or.inr rfl))
    · exfalso
      by_cases hin : T.idx A = n
      · exact hface1 .y2
          (by rw [T.label_shift0 hk (by decide : (1 : HexDir) = 1), if_pos hin])
          (forbidden_of_isX_isY (Or.inr rfl) (Or.inr rfl))
      · exact hnone1 (by rw [T.label_shift0 hk (by decide : (1 : HexDir) = 1), if_neg hin])
    · exfalso
      by_cases hin : T.idx A = n
      · exact hface1 .x2
          (by rw [T.label_shift5 hk (by decide : (1 : HexDir) = 2 + 5), if_pos hin])
          (Or.inl (ForbiddenCore.rule2x (Or.inr rfl) (Or.inr rfl)))
      · exact hface1 (.a (T.idx A))
          (by rw [T.label_shift5 hk (by decide : (1 : HexDir) = 2 + 5), if_neg hin])
          (Or.inl (ForbiddenCore.rule8 hposA (by omega)))
    · exfalso
      by_cases hin : T.idx A = n
      · exact hface2 .x2
          (by rw [T.label_shift5 hk (by decide : (2 : HexDir) = 3 + 5), if_pos hin])
          (Or.inl (ForbiddenCore.rule2x (Or.inr rfl) (Or.inr rfl)))
      · exact hface2 (.a (T.idx A))
          (by rw [T.label_shift5 hk (by decide : (2 : HexDir) = 3 + 5), if_neg hin])
          (Or.inl (ForbiddenCore.rule8 hposA (by omega)))
    · exfalso
      by_cases hi1 : T.idx A = 1
      · exact hface1 .y1
          (by rw [T.label_shift3 hk (by decide : (1 : HexDir) = 4 + 3), if_pos hi1])
          (forbidden_of_isX_isY (Or.inr rfl) (Or.inl rfl))
      · exact hnone1 (by rw [T.label_shift3 hk (by decide : (1 : HexDir) = 4 + 3), if_neg hi1])
    · exfalso
      by_cases hi1 : T.idx A = 1
      · exact hface2 .y1
          (by rw [T.label_shift3 hk (by decide : (2 : HexDir) = 5 + 3), if_pos hi1])
          (forbidden_of_isX_isY (Or.inr rfl) (Or.inl rfl))
      · exact hnone2 (by rw [T.label_shift3 hk (by decide : (2 : HexDir) = 5 + 3), if_neg hi1])
  · -- the flanking stick continues: `A` is the far end of the next stick up the stack
    have hlt : T.idx Wc < n := lt_of_le_of_ne (T.idx_le Wc) hWidx
    have hmem : nbr Wc (T.dir Wc) ∈ T.stickOf Wc := T.nbr_dir_mem_stickOf Wc hlt
    rw [hdW] at hmem
    have hcomm : nbr Wc (u + 5) = nbr A u := by rw [hWc, hA]; exact nbr_comm _ _ _
    have hfx : T.frontCell (T.dir c) x = Wc := by
      rw [frontCell, endCell, if_pos (by rw [hdx, hu]), hu, hWc]
    have hfc : T.frontCell (T.dir c) c = nbr (T.tail c) (T.dir c) := by
      rw [frontCell, endCell, if_pos rfl]
    have hmem2 : Wc ∈ T.stickOf (nbr (T.tail c) (T.dir c)) := by
      have := (T.frontCell_mem_of_sameStack hv h0n (d := T.dir c) (sameAxis_self _) hx).2
      rwa [hfx, hfc] at this
    have hcell : nbr A u ∈ T.stickOf (nbr (T.tail c) (T.dir c)) := by
      rw [← T.stickOf_eq_of_mem hmem2, ← hcomm]
      exact hmem
    obtain ⟨x', hx', hxA⟩ := T.exists_sameStack_of_mem_flankingStick hv hn hL hcell
    have htailA : T.tail x' = A := by
      rw [hu] at hxA
      simpa [nbr] using hxA
    have hdx' : T.dir x' = u := by
      rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx', hu]
    have hdA : T.dir A = u := by
      rw [← htailA, T.dir_tail h0n x', hdx']
    refine ⟨hdA, Or.inl ⟨?_, ?_⟩⟩
    · rw [← htailA]; exact T.idx_tail h0n x'
    · refine SameStack.trans T hx' (T.sameStack_of_stickOf_eq ?_)
      rw [← htailA]
      exact (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n x')).symm

/-- **Mirror image of `dir_backCorner_beyond_tail` on the front side.**  The cell diagonally
beyond the near end (the head) of a stick of a left-leaning stack, on its front side, is again
covered by a horizontal stick of direction `u`; it is either the head of the next stick down the
stack, or an interior cell of a new horizontal stick. -/
theorem dir_frontCorner_beyond_head (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x) :
    T.dir (nbr (T.head x) (u + 2)) = u ∧
      ((T.idx (nbr (T.head x) (u + 2)) = 1 ∧ T.SameStack c (nbr (T.head x) (u + 2))) ∨
        (1 < T.idx (nbr (T.head x) (u + 2)) ∧ T.idx (nbr (T.head x) (u + 2)) < n)) := by
  have h0n : 0 < n := by omega
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx, hu]
  have hdh : T.dir (T.head x) = u := by rw [T.dir_head x, hdx]
  have hih : T.idx (T.head x) = 1 := T.idx_head x
  have hopp : (T.dir c).opp = u + 3 := by rw [hu, opp_eq_add_three]
  set Ec := nbr (T.head x) (u + 3) with hEc
  set A := nbr (T.head x) (u + 2) with hA
  have hdE : T.dir Ec = u + 2 := by
    have h2 := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL hx).2
    rw [hopp, hu] at h2
    exact h2
  have hEA : nbr Ec (u + 1) = A := by
    rw [hEc, hA]
    exact nbr_nbr_of_vec (T.head x) (vec_three_one u)
  by_cases hEidx : T.idx Ec = n
  · -- the flanking stick ends beside the head of `x`: the mirror of the analysis of Figure 12
    have hx1h : T.label (T.head x) (u + 2) = some .x1 := by
      rw [show u + 2 = T.dir (T.head x) + 2 by rw [hdh], T.label_dir_add_two, if_pos hih]
    have hx2E : T.label Ec (u + 1) = some .x2 := by
      rw [T.label_shift5 (u := u) (k := 2) (j := 1) hdE (by decide : (1 : HexDir) = 2 + 5),
        if_pos hEidx]
    have hface5 : ∀ Q, T.label A (u + 5) = some Q → ¬ Forbidden n .x1 Q := fun Q hQ hf =>
      T.clash hv hx1h (by rw [opp_add_two]; exact hQ) hf
    have hnone5 : T.label A (u + 5) ≠ none := fun h =>
      T.no_none hx1h (by rw [opp_add_two]; exact h)
    have hface4 : ∀ Q, T.label A (u + 4) = some Q → ¬ Forbidden n .x2 Q := fun Q hQ hf =>
      T.clash hv hx2E (by rw [hEA, opp_add_one]; exact hQ) hf
    have hnone4 : T.label A (u + 4) ≠ none := fun h =>
      T.no_none hx2E (by rw [hEA, opp_add_one]; exact h)
    have hposA := T.idx_pos A
    have hleA := T.idx_le A
    rcases hexDir_cases u (T.dir A) with hk | hk | hk | hk | hk | hk
    · have hd0 : T.dir A = u + 0 := by rw [hk, add_zero]
      refine ⟨hk, Or.inr ⟨?_, ?_⟩⟩
      · by_contra hi
        have hi1 : T.idx A = 1 := by omega
        exact hface4 .z1
          (by rw [T.label_shift4 hd0 (by decide : (4 : HexDir) = 0 + 4), if_pos hi1])
          (forbidden_of_isX_isZ (Or.inr rfl) (Or.inl rfl))
      · by_contra hi
        have hin : T.idx A = n := by omega
        exact hface5 .x2
          (by rw [T.label_shift5 hd0 (by decide : (5 : HexDir) = 0 + 5), if_pos hin])
          (Or.inl (ForbiddenCore.rule2x (Or.inl rfl) (Or.inr rfl)))
    · exfalso
      by_cases hi1 : T.idx A = 1
      · exact hface4 .y1
          (by rw [T.label_shift3 hk (by decide : (4 : HexDir) = 1 + 3), if_pos hi1])
          (forbidden_of_isX_isY (Or.inr rfl) (Or.inl rfl))
      · exact hnone4 (by rw [T.label_shift3 hk (by decide : (4 : HexDir) = 1 + 3), if_neg hi1])
    · exfalso
      by_cases hi1 : T.idx A = 1
      · exact hface5 .y1
          (by rw [T.label_shift3 hk (by decide : (5 : HexDir) = 2 + 3), if_pos hi1])
          (forbidden_of_isX_isY (Or.inl rfl) (Or.inl rfl))
      · exact hnone5 (by rw [T.label_shift3 hk (by decide : (5 : HexDir) = 2 + 3), if_neg hi1])
    · exfalso
      by_cases hi1 : T.idx A = 1
      · exact hface5 .x1
          (by rw [T.label_shift2 hk (by decide : (5 : HexDir) = 3 + 2), if_pos hi1])
          (Or.inl (ForbiddenCore.rule2x (Or.inl rfl) (Or.inl rfl)))
      · exact hface5 (.c (n + 1 - T.idx A))
          (by rw [T.label_shift2 hk (by decide : (5 : HexDir) = 3 + 2), if_neg hi1])
          (Or.inl (ForbiddenCore.rule6 (by omega) (by omega)))
    · exfalso
      by_cases hin : T.idx A = n
      · exact hface4 .y2
          (by rw [T.label_shift0 hk (by decide : (4 : HexDir) = 4), if_pos hin])
          (forbidden_of_isX_isY (Or.inr rfl) (Or.inr rfl))
      · exact hnone4 (by rw [T.label_shift0 hk (by decide : (4 : HexDir) = 4), if_neg hin])
    · exfalso
      by_cases hin : T.idx A = n
      · exact hface5 .y2
          (by rw [T.label_shift0 hk (by decide : (5 : HexDir) = 5), if_pos hin])
          (forbidden_of_isX_isY (Or.inl rfl) (Or.inr rfl))
      · exact hnone5 (by rw [T.label_shift0 hk (by decide : (5 : HexDir) = 5), if_neg hin])
  · -- the flanking stick continues: `A` is the near end of the next stick down the stack
    have hlt : T.idx Ec < n := lt_of_le_of_ne (T.idx_le Ec) hEidx
    have hmem : nbr Ec (T.dir Ec) ∈ T.stickOf Ec := T.nbr_dir_mem_stickOf Ec hlt
    rw [hdE] at hmem
    have hcomm : nbr Ec (u + 2) = nbr A (u + 3) := by rw [hEc, hA]; exact nbr_comm _ _ _
    have hax : SameAxis (T.dir c).opp (T.dir c) := Or.inr (by rw [HexDir.opp_opp])
    have hnex : T.dir x ≠ (T.dir c).opp := by
      rw [hdx, hopp]; exact (by decide : ∀ a : HexDir, a ≠ a + 3) u
    have hnec : T.dir c ≠ (T.dir c).opp := (by decide : ∀ a : HexDir, a ≠ a.opp) _
    have hfx : T.frontCell (T.dir c).opp x = Ec := by
      rw [frontCell, endCell, if_neg hnex, hopp, hEc]
    have hmem2 : Ec ∈ T.stickOf (T.frontCell (T.dir c).opp c) := by
      have := (T.frontCell_mem_of_sameStack hv h0n hax hx).2
      rwa [hfx] at this
    have hcell : nbr A (u + 3) ∈ T.stickOf (T.frontCell (T.dir c).opp c) := by
      rw [← T.stickOf_eq_of_mem hmem2, ← hcomm]
      exact hmem
    obtain ⟨x', hx', hxA⟩ := T.exists_sameStack_frontCell_eq hv hn hL hax hcell
    have hdx' : T.dir x' = u := by
      rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx', hu]
    have hnex' : T.dir x' ≠ (T.dir c).opp := by
      rw [hdx', hopp]; exact (by decide : ∀ a : HexDir, a ≠ a + 3) u
    rw [frontCell, endCell, if_neg hnex', hopp] at hxA
    have hheadA : T.head x' = A := by simpa [nbr] using hxA
    have hdA : T.dir A = u := by rw [← hheadA, T.dir_head x', hdx']
    refine ⟨hdA, Or.inl ⟨?_, ?_⟩⟩
    · rw [← hheadA]; exact T.idx_head x'
    · refine SameStack.trans T hx' (T.sameStack_of_stickOf_eq ?_)
      rw [← hheadA]
      exact (T.stickOf_eq_of_mem (T.head_mem_stickOf x')).symm

/-! ### Sticks stacked on the back side are parallel -/

/-- **Rule 9: two sticks cannot be stacked back to back.**  If a stick is stacked with another
one in the direction `dir c + 4`, i.e. on its back side, then the two sticks are parallel: their
arrows point the same way. -/
theorem dir_eq_of_stackedBy_add_four (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c c' : Hex}
    (hst : T.StackedBy c c' (T.dir c + 4)) : T.dir c' = T.dir c := by
  rcases hst.2.1 with hd | hd
  · exact hd
  exfalso
  have hd3 : T.dir c' = T.dir c + 3 := by rw [hd, opp_eq_add_three]
  set h0 := T.head c with hh0
  have hdh : T.dir h0 = T.dir c := T.dir_head c
  have hih : T.idx h0 = 1 := T.idx_head c
  have hsth : T.StackedBy h0 c' (T.dir c + 4) :=
    StackedBy.of_mem_stickOf T hst (T.head_mem_stickOf c)
  have hmem : nbr h0 (T.dir c + 4) ∈ T.stickOf c' := hsth.2.2 h0 (T.self_mem_stickOf h0)
  have hdq : T.dir (nbr h0 (T.dir c + 4)) = T.dir c + 3 := by
    rw [T.dir_of_mem_stickOf hmem, hd3]
  have hend := T.endsAt_nbr_of_stackedBy_head hsth hih
  rw [hdh] at hend
  have hiq : T.idx (nbr h0 (T.dir c + 4)) = n := by
    rcases hend with ⟨_, hi⟩ | ⟨hdd, _⟩
    · exact hi
    · rw [HexDir.opp_opp, hdq] at hdd
      exact absurd hdd ((by decide : ∀ a : HexDir, a + 3 ≠ a) (T.dir c))
  have hz1 : T.label h0 (T.dir c + 4) = some .z1 := by
    rw [show T.dir c + 4 = T.dir h0 + 4 by rw [hdh], T.label_dir_add_four, if_pos hih]
  have hb : T.label (nbr h0 (T.dir c + 4)) (T.dir c + 4).opp = some (.b (n - 1)) := by
    rw [opp_add_four,
      T.label_shift4 (u := T.dir c) (k := 3) (by rw [hdq]) (by decide : (1 : HexDir) = 3 + 4),
      if_neg (by omega), hiq]
  exact T.clash hv hz1 hb (Or.inl (ForbiddenCore.rule9 (by omega) (by omega)))

/-- Two sticks stacked on the back side of one of them (in the direction `dir c + 4` or
`dir c + 5`) are parallel. -/
theorem dir_eq_of_stackedBy_back (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c c' : Hex} {e : HexDir}
    (hst : T.StackedBy c c' e) (he : e = T.dir c + 4 ∨ e = T.dir c + 5) : T.dir c' = T.dir c := by
  rcases he with he | he
  · exact T.dir_eq_of_stackedBy_add_four hv hn (by rw [← he]; exact hst)
  · exact T.dir_eq_of_leansLeft hv hn ⟨e, hst, Or.inr he⟩

/-- **The ninth condition of the weave pattern.**  Two sticks of one vertical stack are never
stacked back to back: this is the last field of `StickTiling.IsWeavePattern`, proved for every
valid tiling and every orientation. -/
theorem no_back_to_back_of_satisfiesWeaveRules (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n)
    (u : HexDir) {v v' : Hex}
    (hdv : T.dir v = u + 5) (hst : T.StackedBy v v' (u + 3)) : T.dir v' ≠ u + 2 := by
  have he : u + 3 = T.dir v + 4 := by
    rw [hdv]; exact (by decide : ∀ a : HexDir, a + 3 = a + 5 + 4) u
  have := T.dir_eq_of_stackedBy_add_four hv hn (by rw [← he]; exact hst)
  rw [this, hdv]
  exact (by decide : ∀ a : HexDir, a + 5 ≠ a + 2) u

/-! ### The local structure of the weave pattern -/

/-- **The block of the weave pattern.**  Every valid tiling by sticks of length at least `3`
contains an oriented block of the weave pattern: a left-leaning stack of exactly `n` parallel
horizontal sticks, all with their arrows pointing down (direction `u`), flanked on both sides
by left-slanting sticks whose arrows point away from the stack (directions `u + 5` beyond the
far ends and `u + 2` beyond the near ends), and with horizontal sticks of direction `u` filling
the two cells diagonally beyond its ends. -/
theorem exists_weave_block_of_satisfiesWeaveRules (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) :
    ∃ (u : HexDir) (c : Hex), T.dir c = u ∧ T.IsLeftLeaningStack c ∧ T.stackHeight c = n ∧
      ∀ x, T.SameStack c x →
        T.dir x = u ∧
        T.dir (nbr (T.tail x) u) = u + 5 ∧
        T.dir (nbr (T.head x) (u + 3)) = u + 2 ∧
        T.dir (nbr (T.tail x) (u + 5)) = u ∧
        T.dir (nbr (T.head x) (u + 2)) = u := by
  obtain ⟨c, hL⟩ := T.exists_isLeftLeaningStack hv hn
  refine ⟨T.dir c, c, rfl, hL, T.stackHeight_eq_of_isLeftLeaningStack hv (by omega) hL,
    fun x hx => ⟨T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, ?_, ?_, ?_, ?_⟩⟩
  · exact (T.dir_beyond_ends_of_isLeftLeaningStack hv (by omega) hL hx).1
  · have h2 := (T.dir_beyond_ends_of_isLeftLeaningStack hv (by omega) hL hx).2
    rwa [opp_eq_add_three] at h2
  · exact (T.dir_backCorner_beyond_tail hv (by omega) hL rfl hx).1
  · exact (T.dir_frontCorner_beyond_head hv (by omega) hL rfl hx).1

end StickTiling

end StickPolyhex
