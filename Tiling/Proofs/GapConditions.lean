import Tiling.Proofs.GapSpec
import Tiling.Proofs.MarkedTiling

/-!
# The gap conditions

This file states the *gap conditions* of Section 2.5 of the paper for a schematic whose blocks
carry the marks constructed in `Tiling/Proofs/GapSpec.lean`, and the theorem saying that they
characterise exactly the schematics that respect those marks.

## States and values

A gap of the row `r` lies above a single block of the row `r - 1` (see
`Tiling/Proofs/GapGeometry.lean`), and in fact above a single *bucket* of that block; the index
of that bucket is the **state** of the row `r - 1`, which is the same for all the gaps of the
row `r`.  The state is recorded by a function `st : ℤ → ℕ`, so that the gaps of the row `r + 1`
lie above the bucket `st r`.

A gap of the row `r` therefore lies above the bucket `st (r-1)`, and its **left** and **right
values** are the numbers `x` and `y` for which its left part has length
`(2v-1) (st (r-1) - 1) + x` and its right part length `(2v-1) (s - st (r-1)) + y`; these are the
functions `GapSpec.lval` and `GapSpec.rval` below.

## The conditions

With this notation, `Schematic.GapConditions G S st` collects the conditions of the paper:

* `state_cycle`: the state of the row below a row of state `i` is `σ i`;
* `left_value`, `right_value`: the left (resp. right) value of a gap of a row of state `i` lies
  in `L i` (resp. `R i`);
* `interval`: if a gap has left value `x` and the gap below it to the left has right value `x'`,
  then `x' - x ∈ I` for the interval of the bucket the gap lies above;
* `align_left`, `align_right`: the horizontal alignment of two adjacent rows.  The left end of a
  gap lies at the relative position `v - x'` of the bucket below it, where `x'` is the right
  value of the gap below it to the left, and its right end at the relative position
  `lb - v + y'`, where `y'` is the left value of the gap below it to the right.  (The paper
  states only the consequence `x + y = x' + y'` of these two conditions, which is
  `Schematic.GapConditions.value_sum` below; the alignment itself is used implicitly in the
  paper, and has to be part of the conditions, since the values alone do not determine the
  relative horizontal position of two adjacent rows.)
-/

namespace StickPolyhex

namespace GapSpec

variable (G : GapSpec)

/-- The left value of a gap lying above the bucket `k` whose left part has length `l`. -/
def lval (k l : ℕ) : ℤ := (l : ℤ) - (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1)

/-- The right value of a gap lying above the bucket `k` whose right part has length `m`. -/
def rval (k m : ℕ) : ℤ := (m : ℤ) - (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - k)

end GapSpec

namespace Schematic

/-- The **gap conditions** of Section 2.5 of the paper, for the schematic `S` with the state
function `st` (the gaps of the row `r + 1` lie above the bucket `st r` of the row `r`). -/
structure GapConditions (G : GapSpec) (S : Schematic G.blockLen) (st : ℤ → ℕ) : Prop where
  /-- Every row has a state, one of the `s` buckets. -/
  state_mem : ∀ r, 1 ≤ st r ∧ st r ≤ G.s
  /-- The row below a row of state `i` has state `σ i`. -/
  state_cycle : ∀ r, st (r - 1) = G.sigma (st r)
  /-- The left value of a gap of a row of state `i` lies in `L i`. -/
  left_value : ∀ (r u : ℤ) (l m j : ℕ), S.GapData r u l m j → G.lval (st (r - 1)) l ∈ G.L (st r)
  /-- The right value of a gap of a row of state `i` lies in `R i`. -/
  right_value : ∀ (r u : ℤ) (l m j : ℕ), S.GapData r u l m j → G.rval (st (r - 1)) m ∈ G.R (st r)
  /-- The left end of a gap lies at the relative position `v - x'` of the bucket below it, where
  `x'` is the right value of the gap below it to the left. -/
  align_left : ∀ (r u : ℤ) (l m j : ℕ), S.GapData r u l m j →
    ∀ (uY : ℤ) (lY mY jY : ℕ), S.GapData (r - 1) uY lY mY jY → uY + lY + mY = u - j →
      (j : ℤ) - 2 = ((st (r - 1) : ℤ) - 1) * G.lbZ + G.v - G.rval (st (r - 2)) mY
  /-- The right end of a gap lies at the relative position `lb - v + y'` of the bucket below it,
  where `y'` is the left value of the gap below it to the right. -/
  align_right : ∀ (r u : ℤ) (l m j : ℕ), S.GapData r u l m j →
    ∀ (lZ mZ jZ : ℕ), S.GapData (r - 1) (u - j + G.blockLen + 1) lZ mZ jZ →
      (j : ℤ) + l + m - 2 = (st (r - 1) : ℤ) * G.lbZ - G.v + G.lval (st (r - 2)) lZ
  /-- If a gap has left value `x` and the gap below it to the left has right value `x'`, then
  `x' - x` lies in the interval of the bucket the gap lies above. -/
  interval : ∀ (r u : ℤ) (l m j : ℕ), S.GapData r u l m j →
    ∀ (uY : ℤ) (lY mY jY : ℕ), S.GapData (r - 1) uY lY mY jY → uY + lY + mY = u - j →
      G.Imin (st (r - 1)) ≤ G.rval (st (r - 2)) mY - G.lval (st (r - 1)) l ∧
      G.rval (st (r - 2)) mY - G.lval (st (r - 1)) l ≤ G.Imax (st (r - 1))

/-- A schematic satisfies the gap conditions if it does so for some assignment of states to its
rows. -/
def SatisfiesGapConditions (G : GapSpec) (S : Schematic G.blockLen) : Prop :=
  ∃ st : ℤ → ℕ, S.GapConditions G st

variable {G : GapSpec} {S : Schematic G.blockLen} {st : ℤ → ℕ}

/-- The condition `x + y = x' + y'` of the paper: the sum of the two values of a gap equals the
sum of the right value of the gap below it to the left and of the left value of the gap below it
to the right. -/
theorem GapConditions.value_sum (h : S.GapConditions G st) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j)
    {uY : ℤ} {lY mY jY : ℕ} (hY : S.GapData (r - 1) uY lY mY jY) (heY : uY + lY + mY = u - j)
    {lZ mZ jZ : ℕ} (hZ : S.GapData (r - 1) (u - j + G.blockLen + 1) lZ mZ jZ) :
    G.lval (st (r - 1)) l + G.rval (st (r - 1)) m
      = G.rval (st (r - 2)) mY + G.lval (st (r - 2)) lZ := by
  have h1 := h.align_left r u l m j hg uY lY mY jY hY heY
  have h2 := h.align_right r u l m j hg lZ mZ jZ hZ
  have hlb := G.lbZ_eq
  unfold GapSpec.lval GapSpec.rval at *
  linarith [h1, h2]

end Schematic

end StickPolyhex
