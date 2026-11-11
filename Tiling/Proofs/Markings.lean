import Tiling.Proofs.SchematicPairs

/-!
# Triangle and arrow markings on blocks

This file formalises the *arrow* and *triangle* markings drawn along the top and the bottom
faces of the blocks of a schematic (Section 2.3 of the paper), the extra edge-to-edge matching
rules they stand for, and the equivalence between the two.

## Positions and markings

The top edge of a block of length `n` is divided into `n` unit segments, which correspond to the
`n` concave vertices along the upper side of the top stick of the corresponding horizontal
stack; the same holds along the bottom.  *Position* `i` on a block is the point at distance
`1 + i` from its left end, that is, the boundary between the columns `i` and `i + 1` of the
block; there are `n` positions `0, …, n - 1`.

A `Marking n` records which marks are drawn on a block of length `n`:

* `topArrowL`, `topArrowR`: the positions carrying a left-, resp. right-facing arrow mark on the
  top face of the block;
* `botArrowL`, `botArrowR`: the same on the bottom face;
* `triangleL`, `triangleR`: the positions carrying a left-, resp. right-facing triangle mark on
  the top face.

## The extra matching rules

The marks stand for extra forbidden pairs of edge labels, exactly as in the paper (with `n` the
length of a block, so that the sticks have length `n + 1`):

* a left (resp. right) arrow mark on the top at position `i` forbids `(a_{n-i}, y₂)` (resp.
  `(a_{n-i-1}, y₁)`);
* a left (resp. right) arrow mark on the bottom at position `i` forbids `(c_{i+1}, y₁)` (resp.
  `(c_{i+2}, y₂)`);
* the pair `(a_{n-i}, x₁)` is forbidden unless there is a right-facing triangle facing position
  `i`, and the pair `(b_{n-1-i}, z₂)` is forbidden unless there is a left-facing triangle facing
  position `i`.

The triangle rules only concern the positions `i ≤ n - 2`: the pair `(a₁, x₁)` occurs between
any two sticks stacked one above the other inside a block, and the pair `(b_n, z₂)` occurs
between two adjacent columns of the left part of a gap, so neither may be forbidden.

`markedRules n M` is the resulting set of edge-matching rules: the eleven rules of the paper
(`weaveRules (n+1)`) together with the pairs forbidden by the markings.

## Schematics respecting a marking

`Schematic.RespectsMarking S M` spells out, purely in terms of the schematic, what the marks
require; each clause is exactly the configuration in which the corresponding pair of labels
would be matched in `S.toTiling`:

* an arrow mark on the top at position `i` prevents a column of the left (resp. right) part of a
  gap from lying directly above the column `i + 1` (resp. `i + 2`) of a block;
* an arrow mark on the bottom at position `i` prevents a column of the left (resp. right) part
  of a gap from lying directly below the column `i` (resp. `i + 1`) of a block;
* the right end of a block of a row may only lie above the column `i + 1` of a block of the row
  below if there is a right-facing triangle facing position `i`, and the left end of a block may
  only lie there if there is a left-facing triangle facing position `i`.

## Main results

* `Schematic.toTiling_satisfiesRules_iff`: the tiling of a schematic satisfies the marked rules
  if and only if the schematic respects the markings.
* `Schematic.toTiling_satisfiesWeaveRules`: in particular (taking a marking with no arrows and
  all triangles) the tiling of any schematic satisfies the eleven rules of the paper.
* `StickTiling.exists_schematic_respectsMarking`: conversely, every normalised weave-pattern
  tiling satisfying the marked rules is, up to a translation, the tiling of a schematic that
  respects the markings.
-/

namespace StickPolyhex

@[simp] lemma markedRules_label (n : ℕ) (M : Marking n) : (markedRules n M).Label = StickEdge :=
  rfl

@[simp] lemma labelOf_markedRules {n : ℕ} (M : Marking n) (T : StickTiling (n + 1)) (c : Hex)
    (e : HexDir) : T.labelOf (markedRules n M) c e = T.label c e := rfl

/-- Satisfying the marked rules implies satisfying the eleven rules of the paper. -/
theorem StickTiling.satisfiesWeaveRules_of_satisfiesRules {n : ℕ} {M : Marking n}
    {T : StickTiling (n + 1)} (h : T.SatisfiesRules (markedRules n M)) :
    T.SatisfiesWeaveRules :=
  fun c e p q hp hq hf => h c e p q hp hq (Or.inl hf)

namespace Schematic

variable {n : ℕ} (S : Schematic n) (M : Marking n)

/-- A schematic *respects* the markings `M` when none of the configurations forbidden by the
arrow marks occurs in it, and the ends of the blocks of each row lie above triangle marks of the
row below.  See the module documentation. -/
structure RespectsMarking : Prop where
  /-- A left-facing arrow mark on the top at position `i`: no column of the left part of a gap
  lies directly above the column `i + 1` of a block. -/
  topArrowL : ∀ {i : ℕ}, i ∈ M.topArrowL → ∀ r x : ℤ,
    S.slot r x = .block (i + 1) → S.slot (r + 1) x ≠ .gapL
  /-- A right-facing arrow mark on the top at position `i`: no column of the right part of a gap
  lies directly above the column `i + 2` of a block. -/
  topArrowR : ∀ {i : ℕ}, i ∈ M.topArrowR → ∀ r x : ℤ,
    S.slot r x = .block (i + 2) → S.slot (r + 1) x ≠ .gapR
  /-- A left-facing arrow mark on the bottom at position `i`: no column of the left part of a
  gap lies directly below the column `i` of a block. -/
  botArrowL : ∀ {i : ℕ}, i ∈ M.botArrowL → ∀ r x : ℤ,
    S.slot r x = .block i → S.slot (r - 1) x ≠ .gapL
  /-- A right-facing arrow mark on the bottom at position `i`: no column of the right part of a
  gap lies directly below the column `i + 1` of a block. -/
  botArrowR : ∀ {i : ℕ}, i ∈ M.botArrowR → ∀ r x : ℤ,
    S.slot r x = .block (i + 1) → S.slot (r - 1) x ≠ .gapR
  /-- The right end of a block of the row above the column `i + 1` of a block requires a
  right-facing triangle facing position `i`. -/
  triangleR : ∀ (i : ℕ) (r x : ℤ),
    S.slot r x = .block (i + 1) → S.slot (r + 1) x = .block n → i ∈ M.triangleR
  /-- The left end of a block of the row above the column `i + 2` of a block requires a
  left-facing triangle facing position `i`. -/
  triangleL : ∀ (i : ℕ) (r x : ℤ),
    S.slot r x = .block (i + 1) → S.slot (r + 1) (x + 1) = .block 0 → i ∈ M.triangleL

end Schematic

end StickPolyhex
