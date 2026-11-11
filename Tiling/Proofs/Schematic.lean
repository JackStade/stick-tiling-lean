import Tiling.Proofs.Weave

/-!
# Block schematics

This file formalises the *tiling schematics* of Section 2.3 of the paper (Figure 21).

## The picture

A schematic consists of *rows* of `n × 1` **blocks**.  Between two adjacent blocks of a row there
is a **gap**, which is divided into a left part and a right part, each of length at least one
(so each gap has length at least two).  The left part of a gap is drawn as a right-facing arrow
and the right part as a left-facing arrow.  Finally, the rows are put together so that blocks in
adjacent rows overlap by at least one unit.

A schematic with blocks of length `n` describes a weave-pattern tiling by sticks of length
`n + 1`: every block is a horizontal stack of `n + 1` sticks, and the sticks of the gaps are the
left-slanting sticks, those of the left part of a gap carrying an arrow pointing right and those
of the right part an arrow pointing left.

## The encoding

We record a schematic *column by column*.  Sheared coordinates are used throughout: the cell
`c` of the hexagonal grid lies in **column** `c.1 + c.2` and in **row** `c.2`.  In these
coordinates a horizontal stick occupies `n + 1` consecutive columns of a single row, a
left-slanting stick occupies `n + 1` consecutive rows of a single column, and a block, i.e. a
stack of `n + 1` horizontal sticks each shifted one step to the left with respect to the one
below it, occupies an `(n+1) × (n+1)` square of cells.  The rows of a schematic therefore
correspond to *bands* of `n + 1` consecutive rows of cells, the band `r` consisting of the rows
`(n+1) * r, …, (n+1) * r + n`.

For a row `r` of the schematic and a column `x`, the value `slot r x` records how the column `x`
of the band `r` is used:

* `Slot.block j` (`0 ≤ j ≤ n`): the column is the `j`-th column, counted from the left, of a
  block;
* `Slot.gapL`: the column is a column of the left part of a gap;
* `Slot.gapR`: the column is a column of the right part of a gap.

The conditions of the paper then become the two fields `Schematic.slot_step` and
`Schematic.slot_overlap`:

* `slot_step` says that, reading a row from left to right, the columns of a block are numbered
  `0, 1, …, n`, a block is followed by the left part of a gap, the left part of a gap is followed
  by more of the left part or by the right part, and the right part of a gap is followed by more
  of the right part or by a new block.  In particular every gap has a left part and a right part,
  each of length at least one.
* `slot_overlap` says that a gap column of the row `r + 1` always sits above a block column of the
  row `r` whose index `j` satisfies `2 ≤ j ≤ n - 1`; that is, a gap of a row lies strictly inside
  a block of the row below, leaving at least two columns (i.e. at least one concave corner) of
  that block on either side.  This is the paper's condition that blocks in adjacent rows overlap
  by at least one unit.

(The length of a block is `n` in the paper because the `n + 1` cells of a stick give rise to `n`
concave corners along its upper side; the paper measures lengths in concave corners, while we
count columns of cells.  A gap of length `t` in the paper's sense is a gap of `t` columns here.)

## Main results

* `Schematic.four_le`: a schematic with blocks of length `n` can only exist when `n ≥ 4`, i.e.
  for sticks of length at least `5` — exactly the hypothesis of Lemma 4 of the paper.
* the structure of a row: `Schematic.slot_block_of_block` (the columns of a block are numbered
  consecutively), `Schematic.gapR_of_block_zero`, `Schematic.gapL_of_block_n` (a block is
  preceded and followed by gap columns), `Schematic.exists_gap` (every row has a gap).

The tiling described by a schematic is built in `Tiling/Proofs/SchematicTiling.lean`.
-/

namespace StickPolyhex

/-- A *slot* records how one column of one row of a schematic is used: it is either the `j`-th
column of a block (counted from the left, starting at `0`), or a column of the left part of a
gap, or a column of the right part of a gap. -/
inductive Slot where
  /-- The `j`-th column of a block, counted from the left, starting at `0`. -/
  | block (j : ℕ)
  /-- A column of the left part of a gap (drawn as a right-facing arrow). -/
  | gapL
  /-- A column of the right part of a gap (drawn as a left-facing arrow). -/
  | gapR
  deriving DecidableEq, Repr

namespace Slot

/-- A slot is a *gap slot* when it is a column of a gap, i.e. not a column of a block. -/
def IsGap : Slot → Prop
  | .block _ => False
  | .gapL => True
  | .gapR => True

instance (s : Slot) : Decidable s.IsGap := by
  cases s <;> unfold IsGap <;> infer_instance

@[simp] lemma isGap_gapL : IsGap .gapL := trivial
@[simp] lemma isGap_gapR : IsGap .gapR := trivial
@[simp] lemma not_isGap_block (j : ℕ) : ¬ IsGap (.block j) := id

/-- The slots that may follow one another along a row of a schematic with blocks of length `n`:
inside a block the index increases; the last column of a block is followed by the left part of a
gap; the left part of a gap is followed by the left or the right part; the right part of a gap is
followed by the right part or by the first column of a new block. -/
def Step (n : ℕ) : Slot → Slot → Prop
  | .block j, .block k => j < n ∧ k = j + 1
  | .block j, .gapL => j = n
  | .block _, .gapR => False
  | .gapL, .block _ => False
  | .gapL, .gapL => True
  | .gapL, .gapR => True
  | .gapR, .block k => k = 0
  | .gapR, .gapL => False
  | .gapR, .gapR => True

end Slot

/-- A **tiling schematic** with blocks of length `n`, recorded column by column: `slot r x`
describes the use of the column `x` in the row `r`.  See the module documentation for the
meaning of the two conditions. -/
structure Schematic (n : ℕ) where
  /-- The use of the column `x` of the row `r`. -/
  slot : ℤ → ℤ → Slot
  /-- Reading a row from left to right, consecutive slots follow the pattern
  `block 0, …, block n, gapL, …, gapL, gapR, …, gapR, block 0, …`. -/
  slot_step : ∀ r x, Slot.Step n (slot r x) (slot r (x + 1))
  /-- A gap column of a row lies above a block column of the row below whose index `j` satisfies
  `2 ≤ j ≤ n - 1`: blocks in adjacent rows overlap by at least one unit. -/
  slot_overlap : ∀ r x, (slot (r + 1) x).IsGap → ∃ j, 2 ≤ j ∧ j + 1 ≤ n ∧ slot r x = .block j

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-! ### Reading a row -/

/-- The four possible shapes of a pair of neighbouring columns of a row. -/
lemma step_cases (r x : ℤ) :
    (∃ j, j < n ∧ S.slot r x = .block j ∧ S.slot r (x + 1) = .block (j + 1)) ∨
      (S.slot r x = .block n ∧ S.slot r (x + 1) = .gapL) ∨
      (S.slot r x = .gapL ∧ (S.slot r (x + 1) = .gapL ∨ S.slot r (x + 1) = .gapR)) ∨
      (S.slot r x = .gapR ∧ (S.slot r (x + 1) = .gapR ∨ S.slot r (x + 1) = .block 0)) := by
  have hs := S.slot_step r x
  cases h1 : S.slot r x <;> cases h2 : S.slot r (x + 1) <;>
    rw [h1, h2] at hs <;> simp only [Slot.Step] at hs <;> simp_all

lemma block_le {r x : ℤ} {j : ℕ} (h : S.slot r x = .block j) : j ≤ n := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    (rw [h] at h1; simp_all <;> omega)

lemma step_of_block_lt {r x : ℤ} {j : ℕ} (h : S.slot r x = .block j) (hj : j < n) :
    S.slot r (x + 1) = .block (j + 1) := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h1 <;> simp_all

lemma step_of_block_n {r x : ℤ} (h : S.slot r x = .block n) : S.slot r (x + 1) = .gapL := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h1 <;> simp_all

/-- What can precede the `(j+1)`-st column of a block. -/
lemma pred_of_block_succ {r x : ℤ} {j : ℕ} (h : S.slot r (x + 1) = .block (j + 1)) :
    S.slot r x = .block j := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h2 <;> simp_all

/-- What can precede the first column of a block. -/
lemma pred_of_block_zero {r x : ℤ} (h : S.slot r (x + 1) = .block 0) : S.slot r x = .gapR := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h2 <;> simp_all

/-- What can precede a column of the left part of a gap. -/
lemma pred_of_gapL {r x : ℤ} (h : S.slot r (x + 1) = .gapL) :
    S.slot r x = .block n ∨ S.slot r x = .gapL := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h2 <;> simp_all

/-- What can precede a column of the right part of a gap. -/
lemma pred_of_gapR {r x : ℤ} (h : S.slot r (x + 1) = .gapR) :
    S.slot r x = .gapL ∨ S.slot r x = .gapR := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h2 <;> simp_all

/-- What can follow a column of the left part of a gap. -/
lemma succ_of_gapL {r x : ℤ} (h : S.slot r x = .gapL) :
    S.slot r (x + 1) = .gapL ∨ S.slot r (x + 1) = .gapR := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h1 <;> simp_all

/-- What can follow a column of the right part of a gap. -/
lemma succ_of_gapR {r x : ℤ} (h : S.slot r x = .gapR) :
    S.slot r (x + 1) = .gapR ∨ S.slot r (x + 1) = .block 0 := by
  rcases S.step_cases r x with ⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h] at h1 <;> simp_all

/-! ### The columns of a block -/

/-- Walking left from the `j`-th column of a block reaches its first column. -/
lemma slot_block_zero {r x : ℤ} {j : ℕ} (h : S.slot r x = .block j) :
    S.slot r (x - j) = .block 0 := by
  induction j generalizing x with
  | zero => simpa using h
  | succ k ih =>
    have h' : S.slot r (x - 1 + 1) = .block (k + 1) := by
      rw [show x - 1 + 1 = x by ring]; exact h
    have := ih (S.pred_of_block_succ h')
    rw [show x - ((k + 1 : ℕ) : ℤ) = x - 1 - k by push_cast; ring]
    exact this

/-- Walking right from the first column of a block reaches all of its columns. -/
lemma slot_block_of_zero {r x : ℤ} (h : S.slot r x = .block 0) {k : ℕ} (hk : k ≤ n) :
    S.slot r (x + k) = .block k := by
  induction k with
  | zero => simpa using h
  | succ l ih =>
    have hl := ih (by omega)
    have h2 := S.step_of_block_lt hl (by omega)
    rw [show x + ((l + 1 : ℕ) : ℤ) = x + l + 1 by push_cast; ring]
    exact h2

/-- The columns of a block are numbered `0, 1, …, n` from left to right. -/
lemma slot_block_of_block {r x : ℤ} {j : ℕ} (h : S.slot r x = .block j) {k : ℕ} (hk : k ≤ n) :
    S.slot r (x - j + k) = .block k :=
  S.slot_block_of_zero (S.slot_block_zero h) hk

/-- The column just to the left of a block is a column of the right part of a gap. -/
lemma gapR_of_block_zero {r x : ℤ} (h : S.slot r x = .block 0) : S.slot r (x - 1) = .gapR := by
  refine S.pred_of_block_zero ?_
  rw [show x - 1 + 1 = x by ring]; exact h

/-- The column just to the right of a block is a column of the left part of a gap. -/
lemma gapL_of_block_n {r x : ℤ} {j : ℕ} (h : S.slot r x = .block j) :
    S.slot r (x - j + n + 1) = .gapL :=
  S.step_of_block_n (S.slot_block_of_block h le_rfl)

/-- The column just to the left of a block, seen from any of its columns. -/
lemma gapR_of_block {r x : ℤ} {j : ℕ} (h : S.slot r x = .block j) :
    S.slot r (x - j - 1) = .gapR :=
  S.gapR_of_block_zero (S.slot_block_zero h)

/-! ### Every row contains a gap, and `n ≥ 4` -/

/-- Every row of a schematic has a gap column. -/
lemma exists_gap (r : ℤ) : ∃ x, (S.slot r x).IsGap := by
  cases h : S.slot r 0 with
  | block j => exact ⟨0 - j + n + 1, by rw [S.gapL_of_block_n h]; trivial⟩
  | gapL => exact ⟨0, by rw [h]; trivial⟩
  | gapR => exact ⟨0, by rw [h]; trivial⟩

/-- Every row of a schematic has a column in the left part of a gap. -/
lemma exists_gapL (r : ℤ) : ∃ x, S.slot r x = .gapL := by
  obtain ⟨x, hx⟩ := S.exists_gap r
  cases h : S.slot r x with
  | block j => rw [h] at hx; exact hx.elim
  | gapL => exact ⟨x, h⟩
  | gapR =>
    by_contra hcon
    push_neg at hcon
    -- walking left from a `gapR` column we never leave the right part of the gap
    have key : ∀ k : ℕ, S.slot r (x - k) = .gapR := by
      intro k
      induction k with
      | zero => simpa using h
      | succ l ih =>
        have h1 : S.slot r (x - l - 1 + 1) = .gapR := by
          rw [show x - (l : ℤ) - 1 + 1 = x - l by ring]; exact ih
        rcases S.pred_of_gapR h1 with hL | hR
        · exact absurd hL (hcon _)
        · rw [show x - ((l + 1 : ℕ) : ℤ) = x - l - 1 by push_cast; ring]; exact hR
    -- hence the row below consists of block columns only, which is impossible
    have hb : ∀ k : ℕ, ∃ j, 2 ≤ j ∧ j + 1 ≤ n ∧ S.slot (r - 1) (x - k) = .block j := by
      intro k
      refine S.slot_overlap (r - 1) (x - k) ?_
      rw [show r - 1 + 1 = r by ring, key k]
      trivial
    obtain ⟨j, hj2, hjn, hj⟩ := hb 0
    rw [show x - ((0 : ℕ) : ℤ) = x by simp] at hj
    have hgap : S.slot (r - 1) (x - j - 1) = .gapR := S.gapR_of_block hj
    obtain ⟨j', -, -, hj'⟩ := hb (j + 1)
    rw [show x - ((j + 1 : ℕ) : ℤ) = x - j - 1 by push_cast; ring, hgap] at hj'
    exact Slot.noConfusion hj'

/-- Blocks in a schematic have length at least `4`: schematics describe tilings by sticks of
length at least `5`, which is exactly the hypothesis of Lemma 4 of the paper. -/
lemma four_le (S : Schematic n) : 4 ≤ n := by
  obtain ⟨x, hx⟩ := S.exists_gapL 0
  obtain ⟨j, hj2, hjn, hj⟩ :=
    S.slot_overlap (-1) x (by rw [show (-1 : ℤ) + 1 = 0 by ring, hx]; trivial)
  have hnext : (S.slot ((-1 : ℤ) + 1) (x + 1)).IsGap := by
    rw [show (-1 : ℤ) + 1 = 0 by ring]
    rcases S.succ_of_gapL hx with h | h <;> rw [h] <;> trivial
  obtain ⟨j', hj2', hjn', hj'⟩ := S.slot_overlap (-1) (x + 1) hnext
  have hstep : S.slot (-1) (x + 1) = .block (j + 1) := S.step_of_block_lt hj (by omega)
  rw [hj'] at hstep
  injection hstep with e
  omega

end Schematic

end StickPolyhex
