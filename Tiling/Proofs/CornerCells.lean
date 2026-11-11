import Mathlib.Tactic.Module
import Tiling.Proofs.StackedPairs

/-!
# Stacked pairs fill the concave corners on one side of a stick

The paper describes a *stacked pair* of sticks as a pair of sticks with the same orientation
modulo `π` such that one of them fills all the concave corners on one side of the other.  In
`Tiling/Proofs/StackedPairs.lean` a stacked pair is defined instead as a pair of sticks one of
which is a translate of the other by a unit vector that is not parallel to their common axis.

This file shows that the two descriptions agree: `StickTiling.stackedBy_iff_fillsCorners`.

## Main definitions

* `StickTiling.cornerCells T c g`: the cells filling the concave corners on the side `g` of the
  stick through `c`, that is, the cells `nbr x g` for `x` a cell of the stick which is not its
  last cell.  (Such a cell is adjacent both to `x` and to the next cell `nbr x (T.dir c)` of the
  stick, so it does sit in the corner between two consecutive cells of the stick.)

## Main results

* `StickTiling.stackedBy_iff_fillsCorners`: for sticks of length at least `2`, a stick fills all
  the concave corners on one given side of another stick with the same axis if and only if the
  two sticks form a stacked pair.
-/

namespace StickPolyhex

/-- Translating a walk sideways. -/
lemma nbr_walk (c : Hex) (d g : HexDir) (k : ℤ) :
    nbr (walk c d k) g = walk (nbr c g) d k := by
  simp only [nbr, walk]
  abel

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- The cells filling the concave corners on the side `g` of the stick through `c`: the
neighbours in direction `g` of the cells of the stick other than its last cell. -/
def cornerCells (c : Hex) (g : HexDir) : Finset Hex :=
  ((T.stickOf c).filter fun x => nbr x (T.dir c) ∈ T.stickOf c).image fun x => nbr x g

lemma mem_cornerCells_iff (c : Hex) (g : HexDir) (x : Hex) :
    x ∈ T.cornerCells c g ↔
      ∃ k : ℕ, k + 1 < n ∧ x = walk (nbr (T.head c) g) (T.dir c) k := by
  constructor
  · intro hx
    rw [cornerCells, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Finset.mem_filter, mem_stickOf_iff] at hy
    obtain ⟨⟨k, hk, rfl⟩, hy2⟩ := hy
    refine ⟨k, ?_, ?_⟩
    · rw [cellOfStick, ← walk_succ, mem_stickOf_iff] at hy2
      obtain ⟨j, hj, hje⟩ := hy2
      rw [cellOfStick] at hje
      have := walk_inj (T.head c) (T.dir c) hje
      omega
    · rw [cellOfStick, nbr_walk]
  · rintro ⟨k, hk, rfl⟩
    rw [cornerCells, Finset.mem_image]
    refine ⟨T.cellOfStick c k, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨(T.mem_stickOf_iff c _).2 ⟨k, by omega, rfl⟩, ?_⟩
      rw [cellOfStick, ← walk_succ]
      exact (T.mem_stickOf_iff c _).2 ⟨k + 1, by omega, by rw [cellOfStick]; push_cast; ring_nf⟩
    · rw [cellOfStick, nbr_walk]

/-- A stick whose axis is `d` is a run of `n` consecutive cells in direction `d`, starting from
a suitable base cell. -/
lemma exists_base_of_sameAxis {c' : Hex} {d : HexDir} (hax : SameAxis d (T.dir c')) :
    ∃ q : Hex, ∀ x : Hex, x ∈ T.stickOf c' ↔ ∃ m : ℤ, 0 ≤ m ∧ m < n ∧ x = walk q d m := by
  rcases hax with h | h
  · refine ⟨T.head c', fun x => ?_⟩
    rw [mem_stickOf_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, by omega, by exact_mod_cast hk, by rw [cellOfStick, h]⟩
    · rintro ⟨m, hm0, hmn, rfl⟩
      refine ⟨m.toNat, by omega, ?_⟩
      rw [cellOfStick, h]
      congr 1
      omega
  · refine ⟨walk (T.head c') d (-((n : ℤ) - 1)), fun x => ?_⟩
    rw [mem_stickOf_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(n : ℤ) - 1 - k, by omega, by omega, ?_⟩
      rw [cellOfStick, h, walk_opp, walk_walk]
      congr 1
      omega
    · rintro ⟨m, hm0, hmn, rfl⟩
      refine ⟨((n : ℤ) - 1 - m).toNat, by omega, ?_⟩
      rw [cellOfStick, h, walk_opp, walk_walk]
      congr 1
      omega

/-- **The definition of a stacked pair agrees with the one in the paper.**  Let `g` and `g'` be
the two directions on one side of a stick with axis `d` (so `(g, g') = (d + 1, d + 2)` on one
side and `(g, g') = (d + 5, d + 4)` on the other; note that `g.vec = d.vec + g'.vec`, so that
`nbr x g` is the corner cell between `x` and `nbr x d`).

Then, for sticks of length at least `2`, a second stick fills all the concave corners on the
side `g` of the stick through `c` and has the same axis if and only if the two sticks form a
stacked pair, stacked either by `g` or by `g'`. -/
theorem stackedBy_iff_fillsCorners (hn : 2 ≤ n) {c c' : Hex} {g g' : HexDir}
    (hg : (g = T.dir c + 1 ∧ g' = T.dir c + 2) ∨ (g = T.dir c + 5 ∧ g' = T.dir c + 4)) :
    (SameAxis (T.dir c) (T.dir c') ∧ T.cornerCells c g ⊆ T.stickOf c') ↔
      (T.StackedBy c c' g ∨ T.StackedBy c c' g') := by
  have hvec : g.vec = (T.dir c).vec + g'.vec := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (by decide : ∀ a : HexDir, (a + 1).vec = a.vec + (a + 2).vec) (T.dir c)
    · exact (by decide : ∀ a : HexDir, (a + 5).vec = a.vec + (a + 4).vec) (T.dir c)
  have hng : ¬ SameAxis (T.dir c) g := by
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (by decide : ∀ a : HexDir, ¬ SameAxis a (a + 1)) (T.dir c)
    · exact (by decide : ∀ a : HexDir, ¬ SameAxis a (a + 5)) (T.dir c)
  have hng' : ¬ SameAxis (T.dir c) g' := by
    rcases hg with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (by decide : ∀ a : HexDir, ¬ SameAxis a (a + 2)) (T.dir c)
    · exact (by decide : ∀ a : HexDir, ¬ SameAxis a (a + 4)) (T.dir c)
  -- The corner cell in direction `g` from `x` is also the corner cell in direction `g'` from the
  -- next cell of the stick.
  have hstep : ∀ x : Hex, nbr x g = nbr (nbr x (T.dir c)) g' := by
    intro x
    simp only [nbr, hvec]
    abel
  constructor
  · rintro ⟨hax, hsub⟩
    obtain ⟨q, hq⟩ := T.exists_base_of_sameAxis hax
    set d := T.dir c with hd
    set p := nbr (T.head c) g with hp
    -- the corner cells are `walk p d k` for `k ≤ n - 2`
    have hcorner : ∀ k : ℕ, k + 1 < n → walk p d k ∈ T.stickOf c' := fun k hk =>
      hsub ((T.mem_cornerCells_iff c g _).2 ⟨k, hk, rfl⟩)
    obtain ⟨m0, hm00, hm0n, hm0e⟩ := (hq p).1 (by simpa using hcorner 0 (by omega))
    have hlast := hq (walk p d ((n : ℤ) - 2)) |>.1
      (by
        have := hcorner (n - 2) (by omega)
        have hc : (((n - 2 : ℕ) : ℤ)) = (n : ℤ) - 2 := by omega
        rwa [hc] at this)
    obtain ⟨m1, hm10, hm1n, hm1e⟩ := hlast
    have hm1 : m1 = m0 + ((n : ℤ) - 2) := by
      have : walk q d (m0 + ((n : ℤ) - 2)) = walk q d m1 := by
        rw [← walk_walk, ← hm0e, ← hm1e]
      exact (walk_inj q d this).symm
    have hm0le : m0 ≤ 1 := by omega
    -- every cell of the stick through `c` is `walk (T.head c) d k`
    have hcells : ∀ x ∈ T.stickOf c, ∃ k : ℤ, 0 ≤ k ∧ k < n ∧ x = walk (T.head c) d k := by
      intro x hx
      rw [mem_stickOf_iff] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨k, by omega, by exact_mod_cast hk, rfl⟩
    interval_cases m0
    · -- `p = q`: the partner stick is the translate by `g`
      refine Or.inl ⟨hng, hax, fun x hx => ?_⟩
      obtain ⟨k, hk0, hkn, rfl⟩ := hcells x hx
      refine (hq _).2 ⟨k, hk0, hkn, ?_⟩
      rw [nbr_walk, ← hp, hm0e]
      simp
    · -- `p = walk q d 1`: the partner stick is the translate by `g'`
      refine Or.inr ⟨hng', hax, fun x hx => ?_⟩
      obtain ⟨k, hk0, hkn, rfl⟩ := hcells x hx
      refine (hq _).2 ⟨k, hk0, hkn, ?_⟩
      have hpq : p = walk q d 1 := by rw [hm0e]
      have : nbr (walk (T.head c) d k) g' = walk p d (k - 1) := by
        simp only [nbr, walk, hp, nbr] at *
        have : g'.vec = g.vec - d.vec := by rw [hvec]; abel
        rw [this]
        module
      rw [this, hpq, walk_walk]
      congr 1
      omega
  · rintro (hst | hst)
    · refine ⟨hst.2.1, fun x hx => ?_⟩
      rw [mem_cornerCells_iff] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hmem : walk (T.head c) (T.dir c) k ∈ T.stickOf c :=
        (T.mem_stickOf_iff c _).2 ⟨k, by omega, rfl⟩
      have := hst.2.2 _ hmem
      rwa [nbr_walk] at this
    · refine ⟨hst.2.1, fun x hx => ?_⟩
      rw [mem_cornerCells_iff] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hmem : nbr (walk (T.head c) (T.dir c) k) (T.dir c) ∈ T.stickOf c := by
        rw [← walk_succ]
        exact (T.mem_stickOf_iff c _).2 ⟨k + 1, by omega, by rw [cellOfStick]; push_cast; ring_nf⟩
      have := hst.2.2 _ hmem
      rw [← hstep] at this
      rwa [nbr_walk] at this

end StickTiling

end StickPolyhex
