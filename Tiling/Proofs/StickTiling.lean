import Tiling.Proofs.HexGrid
import Tiling.MainResults.StickDefinitions

/-!
# Tilings of the hexagonal grid by sticks

A *stick of length `n`* is the polyhex formed by `n` hexagons in a row.  Following the paper,
a stick carries an arrow, drawn perpendicular to the row of hexagons; since reflections are not
allowed, a placed stick is determined by the row of cells it occupies together with the arrow,
i.e. by one of the six rotations of the prototile.  Concretely, in the picture of the prototile
the arrow points *down* and the hexagons are numbered `1, …, n` from *right* to *left*;
rotating the picture by `180°` makes the arrow point up and reverses left and right.
Consequently a placed stick is completely described by

* the direction `d` in which the index increases (in the reference picture, `W`), and
* the position of the hexagons along that direction.

This file records a tiling of the plane by sticks of length `n` cell-by-cell: for each cell of
the hexagonal grid we store the orientation `dir` of the stick covering it and the index
`idx ∈ {1, …, n}` of the cell inside that stick.  The `StickTiling` structure consists of these
two pieces of data together with *local consistency rules* saying that these labels really do
come from a tiling by sticks:

* the index always lies in `{1, …, n}`;
* if a cell has index `i < n`, its neighbour in direction `dir` carries the same orientation and
  the index `i + 1`;
* if a cell has index `i > 1`, its neighbour in direction `opp dir` carries the same orientation
  and the index `i - 1`.

The main results of this file justify the definition: the cells sharing a stick with a given
cell form a straight run of exactly `n` cells (`StickTiling.card_stickOf`), every cell lies on
its own stick, and two sticks that meet are equal (`StickTiling.stickOf_eq_of_mem`), so that the
sticks of a `StickTiling` really do partition the hexagonal grid
(`StickTiling.exists_unique_stick`).  An explicit example shows the notion is not vacuous
(`StickTiling.rows`).
-/

namespace StickPolyhex

/-- `walk c d k` is the cell reached from `c` by making `k` steps in direction `d`
(where `k` may be negative, meaning steps in the opposite direction). -/
def walk (c : Hex) (d : HexDir) (k : ℤ) : Hex := c + k • d.vec

@[simp] lemma walk_zero (c : Hex) (d : HexDir) : walk c d 0 = c := by simp [walk]

lemma walk_succ (c : Hex) (d : HexDir) (k : ℤ) : walk c d (k + 1) = nbr (walk c d k) d := by
  simp [walk, nbr, add_smul, add_assoc]

lemma walk_walk (c : Hex) (d : HexDir) (k l : ℤ) : walk (walk c d k) d l = walk c d (k + l) := by
  simp [walk, add_smul, add_assoc]

@[simp] lemma walk_opp (c : Hex) (d : HexDir) (k : ℤ) : walk c d.opp k = walk c d (-k) := by
  simp [walk]

lemma nbr_eq_walk_one (c : Hex) (d : HexDir) : nbr c d = walk c d 1 := by
  simp [walk, nbr]

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- Walking forward along a stick: as long as we stay inside the stick, the orientation is
unchanged and the index increases. -/
lemma dir_walk_forward (c : Hex) :
    ∀ k : ℕ, T.idx c + k ≤ n →
      T.dir (walk c (T.dir c) k) = T.dir c ∧ T.idx (walk c (T.dir c) k) = T.idx c + k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hd, hi⟩ := ih (by omega)
    have hlt : T.idx (walk c (T.dir c) k) < n := by omega
    have hstep : walk c (T.dir c) (k + 1 : ℕ) = nbr (walk c (T.dir c) k) (T.dir c) := by
      have := walk_succ c (T.dir c) (k : ℤ)
      push_cast
      simpa using this
    refine ⟨?_, ?_⟩
    · rw [hstep]
      have := T.succ_dir _ hlt
      rw [hd] at this
      exact this
    · rw [hstep]
      have := T.succ_idx _ hlt
      rw [hd] at this
      omega

/-- Walking backward along a stick: as long as we stay inside the stick, the orientation is
unchanged and the index decreases. -/
lemma dir_walk_backward (c : Hex) :
    ∀ k : ℕ, k < T.idx c →
      T.dir (walk c (T.dir c) (-(k : ℤ))) = T.dir c ∧
        T.idx (walk c (T.dir c) (-(k : ℤ))) = T.idx c - k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hd, hi⟩ := ih (by omega)
    have hlt : 1 < T.idx (walk c (T.dir c) (-(k : ℤ))) := by omega
    have hstep : walk c (T.dir c) (-((k : ℤ) + 1)) =
        nbr (walk c (T.dir c) (-(k : ℤ))) (T.dir c).opp := by
      rw [nbr_eq_walk_one, walk_opp, walk_walk]
      congr 1
      ring
    have hstep' : walk c (T.dir c) (-((k + 1 : ℕ) : ℤ)) =
        nbr (walk c (T.dir c) (-(k : ℤ))) (T.dir c).opp := by
      push_cast
      simpa using hstep
    refine ⟨?_, ?_⟩
    · rw [hstep']
      have := T.pred_dir _ hlt
      rw [hd] at this
      exact this
    · rw [hstep']
      have := T.pred_idx _ hlt
      rw [hd] at this
      omega

/-- The first cell of the stick covering `c`. -/
def head (c : Hex) : Hex := walk c (T.dir c) (-((T.idx c : ℤ) - 1))

@[simp] lemma dir_head (c : Hex) : T.dir (T.head c) = T.dir c := by
  have h := T.dir_walk_backward c (T.idx c - 1) (by have := T.idx_pos c; omega)
  have hc : ((T.idx c - 1 : ℕ) : ℤ) = (T.idx c : ℤ) - 1 := by
    have := T.idx_pos c; omega
  rw [head, ← hc]
  exact h.1

@[simp] lemma idx_head (c : Hex) : T.idx (T.head c) = 1 := by
  have h := T.dir_walk_backward c (T.idx c - 1) (by have := T.idx_pos c; omega)
  have hc : ((T.idx c - 1 : ℕ) : ℤ) = (T.idx c : ℤ) - 1 := by
    have := T.idx_pos c; omega
  rw [head, ← hc, h.2]
  have := T.idx_pos c
  omega

/-- The `k`-th cell (counting from `0`) of the stick covering `c`. -/
def cellOfStick (c : Hex) (k : ℕ) : Hex := walk (T.head c) (T.dir c) k

@[simp] lemma cellOfStick_idx (c : Hex) (k : ℕ) (hk : k < n) :
    T.idx (T.cellOfStick c k) = k + 1 := by
  have h := T.dir_walk_forward (T.head c) k (by rw [T.idx_head]; omega)
  rw [cellOfStick, ← T.dir_head c, h.2, T.idx_head]
  omega

@[simp] lemma cellOfStick_dir (c : Hex) (k : ℕ) (hk : k < n) :
    T.dir (T.cellOfStick c k) = T.dir c := by
  have h := T.dir_walk_forward (T.head c) k (by rw [T.idx_head]; omega)
  rw [cellOfStick, ← T.dir_head c, h.1, T.dir_head]

lemma cellOfStick_idx_sub_one (c : Hex) : T.cellOfStick c (T.idx c - 1) = c := by
  have hpos := T.idx_pos c
  have hc : ((T.idx c - 1 : ℕ) : ℤ) = (T.idx c : ℤ) - 1 := by omega
  rw [cellOfStick, head, hc, walk_walk]
  simp

/-- The stick (as a set of `n` cells) covering the cell `c`. -/
def stickOf (c : Hex) : Finset Hex := (Finset.range n).image (T.cellOfStick c)

lemma mem_stickOf_iff (c x : Hex) :
    x ∈ T.stickOf c ↔ ∃ k < n, T.cellOfStick c k = x := by
  simp [stickOf]

lemma self_mem_stickOf (c : Hex) : c ∈ T.stickOf c := by
  rw [mem_stickOf_iff]
  exact ⟨T.idx c - 1, by have := T.idx_le c; have := T.idx_pos c; omega,
    T.cellOfStick_idx_sub_one c⟩

lemma cellOfStick_injOn (c : Hex) :
    Set.InjOn (T.cellOfStick c) (Finset.range n) := by
  intro k hk l hl hkl
  simp only [Finset.coe_range, Set.mem_Iio] at hk hl
  have h1 : T.idx (T.cellOfStick c k) = k + 1 := T.cellOfStick_idx c k hk
  have h2 : T.idx (T.cellOfStick c l) = l + 1 := T.cellOfStick_idx c l hl
  rw [hkl, h2] at h1
  omega

/-- Every stick consists of exactly `n` cells. -/
@[simp] lemma card_stickOf (c : Hex) : (T.stickOf c).card = n := by
  rw [stickOf, Finset.card_image_of_injOn (T.cellOfStick_injOn c), Finset.card_range]

lemma head_cellOfStick (c : Hex) (k : ℕ) (hk : k < n) :
    T.head (T.cellOfStick c k) = T.head c := by
  have hd : T.dir (T.cellOfStick c k) = T.dir c := T.cellOfStick_dir c k hk
  have hi : T.idx (T.cellOfStick c k) = k + 1 := T.cellOfStick_idx c k hk
  rw [head, hd, hi, cellOfStick, walk_walk]
  push_cast
  ring_nf
  simp

/-- Two sticks that share a cell are equal: the sticks of a stick tiling are pairwise disjoint. -/
lemma stickOf_eq_of_mem {c x : Hex} (hx : x ∈ T.stickOf c) : T.stickOf x = T.stickOf c := by
  rw [mem_stickOf_iff] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [stickOf, stickOf]
  refine Finset.image_congr fun l _ => ?_
  have h1 := T.head_cellOfStick c k hk
  have h2 := T.cellOfStick_dir c k hk
  simp only [cellOfStick] at h1 h2 ⊢
  rw [h1, h2]

/-- The sticks of a stick tiling partition the hexagonal grid: every cell lies in exactly one
stick. -/
theorem exists_unique_stick (x : Hex) :
    ∃! s : Finset Hex, (∃ c, s = T.stickOf c) ∧ x ∈ s := by
  refine ⟨T.stickOf x, ⟨⟨x, rfl⟩, T.self_mem_stickOf x⟩, ?_⟩
  rintro s ⟨⟨c, rfl⟩, hxs⟩
  exact (T.stickOf_eq_of_mem hxs).symm

/-- Each stick is a straight run of `n` consecutive cells in the direction `T.dir c`, starting at
its head. -/
theorem stickOf_eq_image_walk (c : Hex) :
    T.stickOf c = (Finset.range n).image fun k : ℕ => walk (T.head c) (T.dir c) k := rfl

/-- Two cells lie on the same stick if and only if they have the same head. -/
lemma mem_stickOf_iff_head_eq (c x : Hex) :
    x ∈ T.stickOf c ↔ T.head x = T.head c := by
  constructor
  · intro hx
    rw [mem_stickOf_iff] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact T.head_cellOfStick c k hk
  · intro hx
    rw [mem_stickOf_iff]
    refine ⟨T.idx x - 1, by have := T.idx_le x; have := T.idx_pos x; omega, ?_⟩
    have hdx : T.dir x = T.dir c := by
      have h1 : T.dir (T.head x) = T.dir x := T.dir_head x
      have h2 : T.dir (T.head c) = T.dir c := T.dir_head c
      rw [hx] at h1
      rw [h2] at h1
      exact h1.symm
    rw [cellOfStick, ← hx, ← hdx, ← cellOfStick, T.cellOfStick_idx_sub_one x]

end StickTiling

/-!
## An example

A tiling in which every stick is horizontal, with all indices increasing westwards: the cell
`(p, q)` gets index `1 + (-p mod n)`.  This shows that the definition of `StickTiling` is not
vacuous.  (It does *not* satisfy the matching rules of `Tiling/Proofs/MatchingRules.lean`.)
-/

namespace StickTiling

/-- The tiling of the hexagonal grid by horizontal sticks of length `n` laid end to end in each
row, with all arrows pointing the same way. -/
def rows (n : ℕ) (hn : 0 < n) : StickTiling n where
  dir _ := HexDir.W
  idx c := ((-c.1) % (n : ℤ)).toNat + 1
  idx_pos _ := by omega
  idx_le c := by
    have h : (-c.1) % (n : ℤ) < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    have h0 : 0 ≤ (-c.1) % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    omega
  succ_dir _ _ := rfl
  succ_idx c hc := by
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have h0 : 0 ≤ (-c.1) % (n : ℤ) := Int.emod_nonneg _ hn'.ne'
    have hlt : (-c.1) % (n : ℤ) < n := Int.emod_lt_of_pos _ hn'
    have hW : (HexDir.W).vec = (-1, 0) := by decide
    have hnbr : (nbr c HexDir.W).1 = c.1 - 1 := by
      simp [nbr, hW]
      ring
    have hsmall : (-c.1) % (n : ℤ) + 1 < n := by omega
    have key : (-(c.1 - 1)) % (n : ℤ) = (-c.1) % n + 1 := by
      rw [show -(c.1 - 1) = -c.1 + 1 by ring, ← Int.emod_add_emod]
      exact Int.emod_eq_of_lt (by omega) hsmall
    rw [hnbr, key]
    omega
  pred_dir _ _ := rfl
  pred_idx c hc := by
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have h0 : 0 ≤ (-c.1) % (n : ℤ) := Int.emod_nonneg _ hn'.ne'
    have hlt : (-c.1) % (n : ℤ) < n := Int.emod_lt_of_pos _ hn'
    have hW : (HexDir.W).opp.vec = (1, 0) := by decide
    have hnbr : (nbr c (HexDir.W).opp).1 = c.1 + 1 := by
      simp [nbr, hW]
    have hpos : 0 < (-c.1) % (n : ℤ) := by omega
    have key : (-(c.1 + 1)) % (n : ℤ) = (-c.1) % (n : ℤ) - 1 := by
      rw [show -(c.1 + 1) = -c.1 + (-1) by ring, ← Int.emod_add_emod,
        Int.emod_eq_of_lt (by omega) (by omega)]
      ring
    rw [hnbr, key]
    omega

end StickTiling

end StickPolyhex
