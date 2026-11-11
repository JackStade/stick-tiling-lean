import Tiling.Proofs.StackFour

/-!
# Covering the plane by the weave pattern

This file carries out the last step of the proof of Lemma 4 of the paper: the induction of
Figure 18, which propagates the local structure of a left-leaning stack over the whole plane.

The predicate `StickTiling.WeaveCell T u z` says that the cell `z` is covered as in the weave
pattern for the orientation `u`: either by a horizontal stick of direction `u` lying in a
left-leaning (*horizontal*) stack, or by a left-slanting stick lying in a right-leaning
(*vertical*) stack.

The goal of the covering argument, carried out in the files
`Tiling/Proofs/HoleStacks.lean`, `Tiling/Proofs/HoleEnds.lean`,
`Tiling/Proofs/StepStack.lean` and `Tiling/Proofs/StepHole.lean`, is
`StickTiling.exists_weaveCell_all`: in a valid tiling by sticks of length `n ≥ 5` there is an
orientation `u` for which *every* cell is a weave cell.  The proof is a connectivity argument
(`forall_of_nbr_closed`): the hexagonal grid is generated from any one cell by the six
neighbour steps, so it suffices to know that some cell is covered as in the weave pattern and
that the property propagates to neighbours.

The property that is propagated is not `WeaveCell` itself but the stronger predicate
`StickTiling.Anchored`, which remembers *where* a left-slanting stick sits: on a left-leaning
stack from above (`StickTiling.HoleAbove`) or against one from below
(`StickTiling.HoleBelow`).  This extra information is what makes the propagation step for a
left-slanting stick possible, since the matching rules alone do not determine the surroundings
of a stick in isolation.  This file contains the definitions and the elementary facts about
them; the two propagation steps are the theorems `anchored_nbr_of_leftLeaning` and
`anchored_nbr_of_holeAbove`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Weave cells -/

/-- A cell is a *weave cell* for the orientation `u` when it is covered as in the weave pattern:
either by a horizontal stick of direction `u` belonging to a left-leaning (horizontal) stack, or
by a left-slanting stick belonging to a right-leaning (vertical) stack. -/
def WeaveCell (u : HexDir) (z : Hex) : Prop :=
  (T.dir z = u ∧ T.IsLeftLeaningStack z) ∨ (T.SlantsLeft u z ∧ T.IsRightLeaningStack z)

/-- Being a weave cell only depends on the stick through the cell. -/
lemma weaveCell_of_mem_stickOf {u : HexDir} {z p : Hex} (h : T.WeaveCell u z)
    (hp : p ∈ T.stickOf z) : T.WeaveCell u p := by
  have hsame : T.SameStack p z := T.sameStack_of_mem_stickOf hp
  have hdir : T.dir p = T.dir z := T.dir_of_mem_stickOf hp
  rcases h with ⟨hd, hL⟩ | ⟨hs, hR⟩
  · exact Or.inl ⟨by rw [hdir, hd], T.isLeftLeaningStack_of_sameStack hL (SameStack.symm T hsame)⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rcases hs with h | h
      · exact Or.inl (by rw [hdir, h])
      · exact Or.inr (by rw [hdir, h])
    · obtain ⟨a, b, hza, hab⟩ := hR
      exact ⟨a, b, SameStack.trans T hsame hza, hab⟩

/-- Being a weave cell only depends on the stack of the cell, as far as left-leaning stacks are
concerned. -/
lemma weaveCell_of_sameStack_of_dir {u : HexDir} {c z : Hex} (hu : T.dir c = u)
    (hL : T.IsLeftLeaningStack c) (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) (h : T.SameStack c z) :
    T.WeaveCell u z :=
  Or.inl ⟨by rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL h, hu],
    T.isLeftLeaningStack_of_sameStack hL h⟩

/-! ### Anchored cells -/

/-- The cell `z` lies on a left-slanting stick whose lower end rests on a horizontal stick of a
left-leaning stack: `z` lies on one of the sticks of the vertical stack filling the space above
that stack, as described by the analysis of the row above it. -/
def HoleAbove (u : HexDir) (z : Hex) : Prop :=
  ∃ p, T.dir p = u ∧ T.IsLeftLeaningStack p ∧ T.SlantEndAbove u (nbr p (u + 5)) ∧
    z ∈ T.stickOf (nbr p (u + 5))

/-- The mirror image of `StickTiling.HoleAbove`: the cell `z` lies on a left-slanting stick
whose upper end rests against a horizontal stick of a left-leaning stack from below. -/
def HoleBelow (u : HexDir) (z : Hex) : Prop :=
  ∃ p, T.dir p = u ∧ T.IsLeftLeaningStack p ∧ T.SlantEndBelow u (nbr p (u + 2)) ∧
    z ∈ T.stickOf (nbr p (u + 2))

/-- A cell is *anchored* for the orientation `u` when it lies on a horizontal stick of direction
`u` belonging to a left-leaning stack, or on a left-slanting stick resting on such a stack from
above or from below.  This is the invariant that is propagated over the plane; by
`weaveCell_of_anchored` an anchored cell is a weave cell. -/
def Anchored (u : HexDir) (z : Hex) : Prop :=
  (T.dir z = u ∧ T.IsLeftLeaningStack z) ∨ T.HoleAbove u z ∨ T.HoleBelow u z

/-- Being anchored only depends on the stick through the cell. -/
lemma anchored_of_mem_stickOf {u : HexDir} {z p : Hex}
    (h : T.Anchored u z) (hp : p ∈ T.stickOf z) : T.Anchored u p := by
  rcases h with ⟨hd, hL⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
  · exact Or.inl ⟨by rw [T.dir_of_mem_stickOf hp, hd],
      T.isLeftLeaningStack_of_sameStack hL (SameStack.symm T (T.sameStack_of_mem_stickOf hp))⟩
  · exact Or.inr (Or.inl ⟨q, hq.1, hq.2.1, hq.2.2.1,
      by rw [← T.stickOf_eq_of_mem hq.2.2.2]; exact hp⟩)
  · exact Or.inr (Or.inr ⟨q, hq.1, hq.2.1, hq.2.2.1,
      by rw [← T.stickOf_eq_of_mem hq.2.2.2]; exact hp⟩)

/-- A left-slanting stick resting on a left-leaning stack from above really does slant left. -/
lemma slantsLeft_of_holeAbove {u : HexDir} {z : Hex} (h : T.HoleAbove u z) :
    T.SlantsLeft u z := by
  obtain ⟨p, -, -, hslant, hmem⟩ := h
  have hdir : T.dir z = T.dir (nbr p (u + 5)) := T.dir_of_mem_stickOf hmem
  rcases hslant with ⟨hd, -⟩ | ⟨hd, -⟩
  · exact Or.inl (by rw [hdir, hd])
  · exact Or.inr (by rw [hdir, hd])

/-- A left-slanting stick resting against a left-leaning stack from below really does slant
left. -/
lemma slantsLeft_of_holeBelow {u : HexDir} {z : Hex} (h : T.HoleBelow u z) :
    T.SlantsLeft u z := by
  obtain ⟨p, -, -, hslant, hmem⟩ := h
  have hdir : T.dir z = T.dir (nbr p (u + 2)) := T.dir_of_mem_stickOf hmem
  rcases hslant with ⟨hd, -⟩ | ⟨hd, -⟩
  · exact Or.inl (by rw [hdir, hd])
  · exact Or.inr (by rw [hdir, hd])

/-! ### The cells of a left-slanting stick met by a row -/

/-! ### Two adjacent parallel sticks are stacked -/

/-- Two sticks with the same direction and the same index at neighbouring cells are stacked. -/
lemma stackedBy_of_nbr_of_dir_idx_eq {z z' : Hex} {e : HexDir} (hz' : z' = nbr z e)
    (hd : T.dir z' = T.dir z) (hi : T.idx z' = T.idx z) (he : ¬ SameAxis (T.dir z) e) :
    T.StackedBy z z' e := by
  refine ⟨he, by rw [hd]; exact sameAxis_self _, ?_⟩
  have hhead : T.head z' = nbr (T.head z) e := by
    rw [head, head, hd, hi, hz', walk_nbr_comm]
  intro p hp
  rw [T.mem_stickOf_iff] at hp ⊢
  obtain ⟨k, hk, rfl⟩ := hp
  exact ⟨k, hk, by rw [cellOfStick, cellOfStick, hd, hhead, walk_nbr_comm]⟩

/-- The cells of a left-slanting stick whose lower end lies in the row above a stack: they are
the `n` cells obtained by climbing from that end in the direction `u + 5`. -/
lemma stickOf_eq_image_of_slantEndAbove {u : HexDir} {z : Hex}
    (h : T.SlantEndAbove u z) :
    T.stickOf z = (Finset.range n).image (fun k : ℕ => walk z (u + 5) (k : ℤ)) := by
  have hopp : u + 5 = (u + 2).opp := by
    rw [opp_eq_add_three]
    exact (by decide : ∀ a : HexDir, a + 5 = a + 2 + 3) u
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · ext w
    simp only [mem_stickOf_iff, Finset.mem_image, Finset.mem_range]
    have hhead : T.head z = walk z (u + 2) (-((n : ℤ) - 1)) := by
      rw [head, hd, hi]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨n - 1 - k, by omega, ?_⟩
      rw [cellOfStick, hd, hhead, walk_walk, hopp, walk_opp]
      congr 1
      omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨n - 1 - k, by omega, ?_⟩
      rw [cellOfStick, hd, hhead, walk_walk, hopp, walk_opp]
      congr 1
      omega
  · ext w
    simp only [mem_stickOf_iff, Finset.mem_image, Finset.mem_range]
    have hhead : T.head z = z := by rw [head, hi]; simp
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [cellOfStick, hd, hhead]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [cellOfStick, hd, hhead]⟩

/-- Two left-slanting sticks whose ends lie side by side in the row above a stack are stacked
in the direction `u`. -/
lemma stackedBy_of_slantEndAbove_nbr {u : HexDir} {z : Hex}
    (h : T.SlantEndAbove u z) (h' : T.SlantEndAbove u (nbr z u)) : T.StackedBy z (nbr z u) u := by
  refine ⟨?_, ?_, ?_⟩
  · rcases h with ⟨hd, -⟩ | ⟨hd, -⟩
    · rw [hd]; exact (by decide : ∀ a : HexDir, ¬ SameAxis (a + 2) a) u
    · rw [hd]; exact (by decide : ∀ a : HexDir, ¬ SameAxis (a + 5) a) u
  · rcases h with ⟨hd, -⟩ | ⟨hd, -⟩ <;> rcases h' with ⟨hd', -⟩ | ⟨hd', -⟩ <;> rw [hd, hd']
    · exact sameAxis_self _
    · exact (by decide : ∀ a : HexDir, SameAxis (a + 2) (a + 5)) u
    · exact (by decide : ∀ a : HexDir, SameAxis (a + 5) (a + 2)) u
    · exact sameAxis_self _
  · intro p hp
    rw [T.stickOf_eq_image_of_slantEndAbove h] at hp
    rw [T.stickOf_eq_image_of_slantEndAbove h']
    simp only [Finset.mem_image, Finset.mem_range] at hp ⊢
    obtain ⟨k, hk, rfl⟩ := hp
    exact ⟨k, hk, by rw [walk_nbr_comm]⟩

/-- Two left-slanting sticks whose ends lie side by side in the row above a stack form a
right-leaning pair: they belong to one vertical stack. -/
lemma leansRight_of_slantEndAbove_nbr {u : HexDir} {z : Hex}
    (h : T.SlantEndAbove u z) (h' : T.SlantEndAbove u (nbr z u)) : T.LeansRight z (nbr z u) := by
  refine ⟨u, T.stackedBy_of_slantEndAbove_nbr h h', ?_⟩
  rcases h with ⟨hd, -⟩ | ⟨hd, -⟩
  · right; rw [hd]; exact ((by decide : ∀ a : HexDir, a = a + 2 + 4) u)
  · left; rw [hd]; exact ((by decide : ∀ a : HexDir, a = a + 5 + 1) u)

/-- The left-hand one of two left-slanting sticks ending side by side in the row above a stack
lies in a right-leaning stack. -/
lemma isRightLeaningStack_of_slantEndAbove_nbr {u : HexDir} {z : Hex}
    (h : T.SlantEndAbove u z) (h' : T.SlantEndAbove u (nbr z u)) : T.IsRightLeaningStack z :=
  ⟨z, nbr z u, T.sameStack_refl z, T.leansRight_of_slantEndAbove_nbr h h'⟩

/-- The right-hand one of two left-slanting sticks ending side by side in the row above a stack
lies in a right-leaning stack. -/
lemma isRightLeaningStack_of_slantEndAbove_nbr' {u : HexDir} {z : Hex}
    (h : T.SlantEndAbove u z) (h' : T.SlantEndAbove u (nbr z u)) :
    T.IsRightLeaningStack (nbr z u) :=
  ⟨nbr z u, z, T.sameStack_refl _, T.leansRight_symm (T.leansRight_of_slantEndAbove_nbr h h')⟩

/-- Being in a right-leaning stack only depends on the stack. -/
lemma isRightLeaningStack_of_sameStack {c z : Hex} (hR : T.IsRightLeaningStack c)
    (hz : T.SameStack c z) : T.IsRightLeaningStack z := by
  obtain ⟨a, b, hca, hab⟩ := hR
  exact ⟨a, b, SameStack.trans T (SameStack.symm T hz) hca, hab⟩

/-- The cells of a left-slanting stick whose upper end lies in the row below a stack: they are
the `n` cells obtained by descending from that end in the direction `u + 2`. -/
lemma stickOf_eq_image_of_slantEndBelow {u : HexDir} {z : Hex}
    (h : T.SlantEndBelow u z) :
    T.stickOf z = (Finset.range n).image (fun k : ℕ => walk z (u + 2) (k : ℤ)) := by
  have hopp : u + 2 = (u + 5).opp := by
    rw [opp_eq_add_three]
    exact (by decide : ∀ a : HexDir, a + 2 = a + 5 + 3) u
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · ext w
    simp only [mem_stickOf_iff, Finset.mem_image, Finset.mem_range]
    have hhead : T.head z = z := by rw [head, hi]; simp
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [cellOfStick, hd, hhead]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [cellOfStick, hd, hhead]⟩
  · ext w
    simp only [mem_stickOf_iff, Finset.mem_image, Finset.mem_range]
    have hhead : T.head z = walk z (u + 5) (-((n : ℤ) - 1)) := by
      rw [head, hd, hi]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨n - 1 - k, by omega, ?_⟩
      rw [cellOfStick, hd, hhead, walk_walk, hopp, walk_opp]
      congr 1
      omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨n - 1 - k, by omega, ?_⟩
      rw [cellOfStick, hd, hhead, walk_walk, hopp, walk_opp]
      congr 1
      omega

/-- Two left-slanting sticks whose ends lie side by side in the row below a stack are stacked
in the direction `u`. -/
lemma stackedBy_of_slantEndBelow_nbr {u : HexDir} {z : Hex}
    (h : T.SlantEndBelow u z) (h' : T.SlantEndBelow u (nbr z u)) : T.StackedBy z (nbr z u) u := by
  refine ⟨?_, ?_, ?_⟩
  · rcases h with ⟨hd, -⟩ | ⟨hd, -⟩
    · rw [hd]; exact (by decide : ∀ a : HexDir, ¬ SameAxis (a + 2) a) u
    · rw [hd]; exact (by decide : ∀ a : HexDir, ¬ SameAxis (a + 5) a) u
  · rcases h with ⟨hd, -⟩ | ⟨hd, -⟩ <;> rcases h' with ⟨hd', -⟩ | ⟨hd', -⟩ <;> rw [hd, hd']
    · exact sameAxis_self _
    · exact (by decide : ∀ a : HexDir, SameAxis (a + 2) (a + 5)) u
    · exact (by decide : ∀ a : HexDir, SameAxis (a + 5) (a + 2)) u
    · exact sameAxis_self _
  · intro p hp
    rw [T.stickOf_eq_image_of_slantEndBelow h] at hp
    rw [T.stickOf_eq_image_of_slantEndBelow h']
    simp only [Finset.mem_image, Finset.mem_range] at hp ⊢
    obtain ⟨k, hk, rfl⟩ := hp
    exact ⟨k, hk, by rw [walk_nbr_comm]⟩

/-- Two left-slanting sticks whose ends lie side by side in the row below a stack form a
right-leaning pair. -/
lemma leansRight_of_slantEndBelow_nbr {u : HexDir} {z : Hex}
    (h : T.SlantEndBelow u z) (h' : T.SlantEndBelow u (nbr z u)) : T.LeansRight z (nbr z u) := by
  refine ⟨u, T.stackedBy_of_slantEndBelow_nbr h h', ?_⟩
  rcases h with ⟨hd, -⟩ | ⟨hd, -⟩
  · right; rw [hd]; exact ((by decide : ∀ a : HexDir, a = a + 2 + 4) u)
  · left; rw [hd]; exact ((by decide : ∀ a : HexDir, a = a + 5 + 1) u)

/-- The left-hand one of two left-slanting sticks ending side by side in the row below a stack
lies in a right-leaning stack. -/
lemma isRightLeaningStack_of_slantEndBelow_nbr {u : HexDir} {z : Hex}
    (h : T.SlantEndBelow u z) (h' : T.SlantEndBelow u (nbr z u)) : T.IsRightLeaningStack z :=
  ⟨z, nbr z u, T.sameStack_refl z, T.leansRight_of_slantEndBelow_nbr h h'⟩

/-- The right-hand one of two left-slanting sticks ending side by side in the row below a stack
lies in a right-leaning stack. -/
lemma isRightLeaningStack_of_slantEndBelow_nbr' {u : HexDir} {z : Hex}
    (h : T.SlantEndBelow u z) (h' : T.SlantEndBelow u (nbr z u)) :
    T.IsRightLeaningStack (nbr z u) :=
  ⟨nbr z u, z, T.sameStack_refl _, T.leansRight_symm (T.leansRight_of_slantEndBelow_nbr h h')⟩

/-! ### From one weave cell to the whole plane -/

/-- The hexagonal grid is generated from any cell by the six neighbour steps: a predicate that
holds at one cell and is stable under passing to a neighbour holds everywhere. -/
lemma forall_of_nbr_closed {P : Hex → Prop} {z₀ : Hex} (h₀ : P z₀)
    (hstep : ∀ z, P z → ∀ e, P (nbr z e)) : ∀ z, P z := by
  have hE : ∀ z, P z → P (z + (1, 0)) := fun z hz => by
    have h := hstep z hz HexDir.E
    have hv : (HexDir.E).vec = ((1 : ℤ), (0 : ℤ)) := by decide
    rwa [nbr, hv] at h
  have hW : ∀ z, P z → P (z + (-1, 0)) := fun z hz => by
    have h := hstep z hz HexDir.W
    have hv : (HexDir.W).vec = ((-1 : ℤ), (0 : ℤ)) := by decide
    rwa [nbr, hv] at h
  have hNE : ∀ z, P z → P (z + (0, 1)) := fun z hz => by
    have h := hstep z hz HexDir.NE
    have hv : (HexDir.NE).vec = ((0 : ℤ), (1 : ℤ)) := by decide
    rwa [nbr, hv] at h
  have hSW : ∀ z, P z → P (z + (0, -1)) := fun z hz => by
    have h := hstep z hz HexDir.SW
    have hv : (HexDir.SW).vec = ((0 : ℤ), (-1 : ℤ)) := by decide
    rwa [nbr, hv] at h
  have hrow : ∀ k : ℤ, P (z₀ + (k, 0)) := by
    intro k
    induction k using Int.induction_on with
    | zero =>
      have heq : z₀ + ((0 : ℤ), (0 : ℤ)) = z₀ := by simp
      rwa [heq]
    | succ i ih =>
      have h := hE _ ih
      have heq : z₀ + ((i : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ)) = z₀ + (((i : ℤ) + 1), (0 : ℤ)) := by
        simp [Prod.ext_iff]; ring
      rwa [heq] at h
    | pred i ih =>
      have h := hW _ ih
      have heq : z₀ + ((-(i : ℤ)), (0 : ℤ)) + ((-1 : ℤ), (0 : ℤ))
          = z₀ + ((-(i : ℤ) - 1), (0 : ℤ)) := by
        simp [Prod.ext_iff]; ring
      rwa [heq] at h
  have hall : ∀ k l : ℤ, P (z₀ + (k, l)) := by
    intro k l
    induction l using Int.induction_on with
    | zero => simpa using hrow k
    | succ i ih =>
      have h := hNE _ ih
      have heq : z₀ + (k, (i : ℤ)) + ((0 : ℤ), (1 : ℤ)) = z₀ + (k, ((i : ℤ) + 1)) := by
        simp [Prod.ext_iff]; ring
      rwa [heq] at h
    | pred i ih =>
      have h := hSW _ ih
      have heq : z₀ + (k, (-(i : ℤ))) + ((0 : ℤ), (-1 : ℤ)) = z₀ + (k, (-(i : ℤ) - 1)) := by
        simp [Prod.ext_iff]; ring
      rwa [heq] at h
  intro z
  have h := hall (z.1 - z₀.1) (z.2 - z₀.2)
  have heq : z₀ + (z.1 - z₀.1, z.2 - z₀.2) = z := by simp [Prod.ext_iff]
  rwa [heq] at h

end StickTiling

end StickPolyhex
