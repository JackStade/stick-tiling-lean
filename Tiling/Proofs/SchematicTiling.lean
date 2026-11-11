import Tiling.Proofs.Schematic

/-!
# The tiling described by a schematic

This file turns a schematic with blocks of length `n` (see `Tiling/Proofs/Schematic.lean`) into
a tiling of the hexagonal grid by sticks of length `n + 1`, and computes the basic data of that
tiling (the direction and the index of every cell, the head of every stick, and the cells of
every stick).

## Sheared coordinates

The cell `c` of the hexagonal grid lies in the **column** `shearCol c = c.1 + c.2` and the
**row** `shearRow c = c.2`; conversely `shearCell x q` is the cell in column `x` and row `q`.
In these coordinates:

* a step west (`HexDir.W`) decreases the column by one and keeps the row;
* a step north-west (`HexDir.NW`) keeps the column and increases the row by one;
* a step south-east (`HexDir.SE`) keeps the column and decreases the row by one.

So horizontal sticks (direction `W`) run along a row, and left-slanting sticks (directions `NW`
and `SE`) run along a column.  The rows of the grid are grouped into **bands** of `n + 1`
consecutive rows; the band of the row `q` is `bandRow n q = q / (n+1)` and the position of `q`
inside its band is `subRow n q = q % (n+1)`.

## The tiling

A cell `c` of the grid is used according to the slot `S.slotAt c` of its column in its band:

* `Slot.block j`: `c` belongs to a horizontal stick, of direction `W` (the arrow points down),
  which is the `j`-th column of a block; the index of `c` in its stick is `n + 1 - j`;
* `Slot.gapL`: `c` belongs to a left-slanting stick of direction `SE` (arrow pointing right)
  filling one column of the left part of a gap; the stick occupies the whole band, and the index
  of `c` is `n + 1 - i` where `i` is the position of the row of `c` in its band;
* `Slot.gapR`: `c` belongs to a left-slanting stick of direction `NW` (arrow pointing left)
  filling one column of the right part of a gap; the index of `c` is `i + 1`.

`Schematic.toTiling` packages this as a `StickTiling (n+1)`.
-/

namespace StickPolyhex

/-! ### Sheared coordinates -/

/-- The column of a cell in sheared coordinates. -/
def shearCol (c : Hex) : ℤ := c.1 + c.2

/-- The row of a cell. -/
def shearRow (c : Hex) : ℤ := c.2

/-- The cell in column `x` and row `q`. -/
def shearCell (x q : ℤ) : Hex := (x - q, q)

@[simp] lemma shearCol_shearCell (x q : ℤ) : shearCol (shearCell x q) = x := by
  simp [shearCol, shearCell]

@[simp] lemma shearRow_shearCell (x q : ℤ) : shearRow (shearCell x q) = q := rfl

@[simp] lemma shearCell_shear (c : Hex) : shearCell (shearCol c) (shearRow c) = c := by
  simp [shearCol, shearRow, shearCell]

lemma hex_ext {c c' : Hex} (hx : shearCol c = shearCol c') (hq : shearRow c = shearRow c') :
    c = c' := by
  rw [← shearCell_shear c, ← shearCell_shear c', hx, hq]

@[simp] lemma shearCol_nbr_W (c : Hex) : shearCol (nbr c HexDir.W) = shearCol c - 1 := by
  simp [shearCol, nbr, HexDir.vec, HexDir.W]; ring

@[simp] lemma shearRow_nbr_W (c : Hex) : shearRow (nbr c HexDir.W) = shearRow c := by
  simp [shearRow, nbr, HexDir.vec, HexDir.W]

@[simp] lemma shearCol_nbr_E (c : Hex) : shearCol (nbr c HexDir.E) = shearCol c + 1 := by
  simp [shearCol, nbr, HexDir.vec, HexDir.E]; ring

@[simp] lemma shearRow_nbr_E (c : Hex) : shearRow (nbr c HexDir.E) = shearRow c := by
  simp [shearRow, nbr, HexDir.vec, HexDir.E]

@[simp] lemma shearCol_nbr_NW (c : Hex) : shearCol (nbr c HexDir.NW) = shearCol c := by
  simp [shearCol, nbr, HexDir.vec, HexDir.NW]; ring

@[simp] lemma shearRow_nbr_NW (c : Hex) : shearRow (nbr c HexDir.NW) = shearRow c + 1 := by
  simp [shearRow, nbr, HexDir.vec, HexDir.NW]

@[simp] lemma shearCol_nbr_SE (c : Hex) : shearCol (nbr c HexDir.SE) = shearCol c := by
  simp [shearCol, nbr, HexDir.vec, HexDir.SE]; ring

@[simp] lemma shearRow_nbr_SE (c : Hex) : shearRow (nbr c HexDir.SE) = shearRow c - 1 := by
  simp [shearRow, nbr, HexDir.vec, HexDir.SE]; ring

@[simp] lemma shearCol_nbr_NE (c : Hex) : shearCol (nbr c HexDir.NE) = shearCol c + 1 := by
  simp [shearCol, nbr, HexDir.vec, HexDir.NE]; ring

@[simp] lemma shearRow_nbr_NE (c : Hex) : shearRow (nbr c HexDir.NE) = shearRow c + 1 := by
  simp [shearRow, nbr, HexDir.vec, HexDir.NE]

@[simp] lemma shearCol_nbr_SW (c : Hex) : shearCol (nbr c HexDir.SW) = shearCol c - 1 := by
  simp [shearCol, nbr, HexDir.vec, HexDir.SW]; ring

@[simp] lemma shearRow_nbr_SW (c : Hex) : shearRow (nbr c HexDir.SW) = shearRow c - 1 := by
  simp [shearRow, nbr, HexDir.vec, HexDir.SW]; ring

/-! ### Bands -/

/-- The band of the row `q`: the rows of the grid are grouped into bands of `n + 1` consecutive
rows, the band `r` consisting of the rows `(n+1) * r, …, (n+1) * r + n`. -/
def bandRow (n : ℕ) (q : ℤ) : ℤ := q / (n + 1)

/-- The position of the row `q` inside its band, a number in `{0, …, n}`. -/
def subRow (n : ℕ) (q : ℤ) : ℤ := q % (n + 1)

lemma subRow_nonneg (n : ℕ) (q : ℤ) : 0 ≤ subRow n q :=
  Int.emod_nonneg _ (by positivity)

lemma subRow_le (n : ℕ) (q : ℤ) : subRow n q ≤ n := by
  have := Int.emod_lt_of_pos q (show (0 : ℤ) < (n : ℤ) + 1 by positivity)
  unfold subRow
  omega

lemma bandRow_mul_add (n : ℕ) (q : ℤ) : ((n : ℤ) + 1) * bandRow n q + subRow n q = q :=
  Int.mul_ediv_add_emod q _

lemma bandRow_subRow_eq (n : ℕ) (r i : ℤ) (h0 : 0 ≤ i) (hi : i ≤ n) :
    bandRow n (((n : ℤ) + 1) * r + i) = r ∧ subRow n (((n : ℤ) + 1) * r + i) = i := by
  have h : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  exact (Int.ediv_emod_unique (a := ((n : ℤ) + 1) * r + i) (b := (n : ℤ) + 1) (q := r) (r := i) h).2
    ⟨by ring, h0, by omega⟩

lemma bandRow_eq (n : ℕ) (r i : ℤ) (h0 : 0 ≤ i) (hi : i ≤ n) :
    bandRow n (((n : ℤ) + 1) * r + i) = r := (bandRow_subRow_eq n r i h0 hi).1

lemma subRow_eq (n : ℕ) (r i : ℤ) (h0 : 0 ≤ i) (hi : i ≤ n) :
    subRow n (((n : ℤ) + 1) * r + i) = i := (bandRow_subRow_eq n r i h0 hi).2

/-- Moving up one row inside a band. -/
lemma bandRow_succ_of_lt {n : ℕ} {q : ℤ} (h : subRow n q < n) :
    bandRow n (q + 1) = bandRow n q ∧ subRow n (q + 1) = subRow n q + 1 := by
  have h0 := subRow_nonneg n q
  have hrw : q + 1 = ((n : ℤ) + 1) * bandRow n q + (subRow n q + 1) := by
    linarith [bandRow_mul_add n q]
  rw [hrw]
  exact ⟨bandRow_eq n _ _ (by omega) (by omega), subRow_eq n _ _ (by omega) (by omega)⟩

/-- Moving down one row inside a band. -/
lemma bandRow_pred_of_pos {n : ℕ} {q : ℤ} (h : 0 < subRow n q) :
    bandRow n (q - 1) = bandRow n q ∧ subRow n (q - 1) = subRow n q - 1 := by
  have hle := subRow_le n q
  have hrw : q - 1 = ((n : ℤ) + 1) * bandRow n q + (subRow n q - 1) := by
    linarith [bandRow_mul_add n q]
  rw [hrw]
  exact ⟨bandRow_eq n _ _ (by omega) (by omega), subRow_eq n _ _ (by omega) (by omega)⟩

/-- Moving up one row out of the top of a band. -/
lemma bandRow_succ_of_eq_n {n : ℕ} {q : ℤ} (h : subRow n q = n) :
    bandRow n (q + 1) = bandRow n q + 1 := by
  have hrw : q + 1 = ((n : ℤ) + 1) * (bandRow n q + 1) + 0 := by
    have := bandRow_mul_add n q; rw [h] at this; linarith
  rw [hrw]
  exact bandRow_eq n _ _ le_rfl (by positivity)

/-- Moving down one row out of the bottom of a band. -/
lemma bandRow_pred_of_eq_zero {n : ℕ} {q : ℤ} (h : subRow n q = 0) :
    bandRow n (q - 1) = bandRow n q - 1 := by
  have hrw : q - 1 = ((n : ℤ) + 1) * (bandRow n q - 1) + n := by
    have := bandRow_mul_add n q; rw [h] at this; linarith
  rw [hrw]
  exact bandRow_eq n _ _ (by positivity) le_rfl

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-- The band of a cell. -/
def bandOf (_S : Schematic n) (c : Hex) : ℤ := bandRow n (shearRow c)

/-- The position of a cell inside its band. -/
def subOf (_S : Schematic n) (c : Hex) : ℤ := subRow n (shearRow c)

/-- The slot of a cell: how the column of the cell is used in the band of the cell. -/
def slotAt (c : Hex) : Slot := S.slot (S.bandOf c) (shearCol c)

/-- The direction of the stick covering a cell. -/
def dirAt (c : Hex) : HexDir :=
  match S.slotAt c with
  | .block _ => HexDir.W
  | .gapL => HexDir.SE
  | .gapR => HexDir.NW

/-- The index of a cell inside the stick covering it. -/
def idxAt (c : Hex) : ℕ :=
  match S.slotAt c with
  | .block j => n + 1 - j
  | .gapL => (n - S.subOf c).toNat + 1
  | .gapR => (S.subOf c).toNat + 1

@[simp] lemma dirAt_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.dirAt c = HexDir.W := by rw [dirAt, h]

@[simp] lemma dirAt_gapL {c : Hex} (h : S.slotAt c = .gapL) : S.dirAt c = HexDir.SE := by
  rw [dirAt, h]

@[simp] lemma dirAt_gapR {c : Hex} (h : S.slotAt c = .gapR) : S.dirAt c = HexDir.NW := by
  rw [dirAt, h]

@[simp] lemma idxAt_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.idxAt c = n + 1 - j := by rw [idxAt, h]

@[simp] lemma idxAt_gapL {c : Hex} (h : S.slotAt c = .gapL) :
    S.idxAt c = (n - S.subOf c).toNat + 1 := by rw [idxAt, h]

@[simp] lemma idxAt_gapR {c : Hex} (h : S.slotAt c = .gapR) :
    S.idxAt c = (S.subOf c).toNat + 1 := by rw [idxAt, h]

lemma subOf_nonneg (c : Hex) : 0 ≤ S.subOf c := subRow_nonneg n _
lemma subOf_le (c : Hex) : S.subOf c ≤ n := subRow_le n _

/-! ### Neighbouring cells -/

lemma slotAt_nbr_W (c : Hex) : S.slotAt (nbr c HexDir.W) = S.slot (S.bandOf c) (shearCol c - 1) := by
  rw [slotAt, bandOf, shearRow_nbr_W, shearCol_nbr_W, bandOf]

lemma slotAt_nbr_E (c : Hex) : S.slotAt (nbr c HexDir.E) = S.slot (S.bandOf c) (shearCol c + 1) := by
  rw [slotAt, bandOf, shearRow_nbr_E, shearCol_nbr_E, bandOf]

lemma slotAt_nbr_NW {c : Hex} (h : S.subOf c < n) : S.slotAt (nbr c HexDir.NW) = S.slotAt c := by
  rw [slotAt, slotAt, bandOf, bandOf, shearRow_nbr_NW, shearCol_nbr_NW,
    (bandRow_succ_of_lt (n := n) h).1]

lemma subOf_nbr_NW {c : Hex} (h : S.subOf c < n) : S.subOf (nbr c HexDir.NW) = S.subOf c + 1 := by
  rw [subOf, subOf, shearRow_nbr_NW, (bandRow_succ_of_lt (n := n) h).2]

lemma slotAt_nbr_SE {c : Hex} (h : 0 < S.subOf c) : S.slotAt (nbr c HexDir.SE) = S.slotAt c := by
  rw [slotAt, slotAt, bandOf, bandOf, shearRow_nbr_SE, shearCol_nbr_SE,
    (bandRow_pred_of_pos (n := n) h).1]

lemma subOf_nbr_SE {c : Hex} (h : 0 < S.subOf c) : S.subOf (nbr c HexDir.SE) = S.subOf c - 1 := by
  rw [subOf, subOf, shearRow_nbr_SE, (bandRow_pred_of_pos (n := n) h).2]

/-! ### The tiling -/

/-- The tiling of the hexagonal grid by sticks of length `n + 1` described by a schematic with
blocks of length `n`. -/
def toTiling : StickTiling (n + 1) where
  dir := S.dirAt
  idx := S.idxAt
  idx_pos c := by
    cases h : S.slotAt c with
    | block j => rw [S.idxAt_block h]; have := S.block_le (r := S.bandOf c) (x := shearCol c) h; omega
    | gapL => rw [S.idxAt_gapL h]; omega
    | gapR => rw [S.idxAt_gapR h]; omega
  idx_le c := by
    have h0 := S.subOf_nonneg c
    have hn := S.subOf_le c
    cases h : S.slotAt c with
    | block j => rw [S.idxAt_block h]; omega
    | gapL => rw [S.idxAt_gapL h]; omega
    | gapR => rw [S.idxAt_gapR h]; omega
  succ_dir c hc := by
    have h0 := S.subOf_nonneg c
    have hn := S.subOf_le c
    cases h : S.slotAt c with
    | block j =>
      have hj : 1 ≤ j := by
        rw [S.idxAt_block h] at hc
        have := S.block_le (r := S.bandOf c) (x := shearCol c) h
        omega
      have hW : S.slotAt (nbr c HexDir.W) = .block (j - 1) := by
        rw [S.slotAt_nbr_W]
        refine S.pred_of_block_succ ?_
        rw [show shearCol c - 1 + 1 = shearCol c by ring, show j - 1 + 1 = j by omega]
        exact h
      rw [S.dirAt_block h, S.dirAt_block hW]
    | gapL =>
      have hs : 0 < S.subOf c := by
        rw [S.idxAt_gapL h] at hc; omega
      rw [S.dirAt_gapL h, S.dirAt_gapL (by rw [S.slotAt_nbr_SE hs, h])]
    | gapR =>
      have hs : S.subOf c < n := by
        rw [S.idxAt_gapR h] at hc; omega
      rw [S.dirAt_gapR h, S.dirAt_gapR (by rw [S.slotAt_nbr_NW hs, h])]
  succ_idx c hc := by
    have h0 := S.subOf_nonneg c
    have hn := S.subOf_le c
    cases h : S.slotAt c with
    | block j =>
      have hjn := S.block_le (r := S.bandOf c) (x := shearCol c) h
      have hj : 1 ≤ j := by rw [S.idxAt_block h] at hc; omega
      have hW : S.slotAt (nbr c HexDir.W) = .block (j - 1) := by
        rw [S.slotAt_nbr_W]
        refine S.pred_of_block_succ ?_
        rw [show shearCol c - 1 + 1 = shearCol c by ring, show j - 1 + 1 = j by omega]
        exact h
      rw [S.dirAt_block h, S.idxAt_block hW, S.idxAt_block h]
      omega
    | gapL =>
      have hs : 0 < S.subOf c := by rw [S.idxAt_gapL h] at hc; omega
      have hSE : S.slotAt (nbr c HexDir.SE) = .gapL := by rw [S.slotAt_nbr_SE hs, h]
      rw [S.dirAt_gapL h, S.idxAt_gapL hSE, S.idxAt_gapL h, S.subOf_nbr_SE hs]
      omega
    | gapR =>
      have hs : S.subOf c < n := by rw [S.idxAt_gapR h] at hc; omega
      have hNW : S.slotAt (nbr c HexDir.NW) = .gapR := by rw [S.slotAt_nbr_NW hs, h]
      rw [S.dirAt_gapR h, S.idxAt_gapR hNW, S.idxAt_gapR h, S.subOf_nbr_NW hs]
      omega
  pred_dir c hc := by
    have h0 := S.subOf_nonneg c
    have hn := S.subOf_le c
    cases h : S.slotAt c with
    | block j =>
      have hjn := S.block_le (r := S.bandOf c) (x := shearCol c) h
      have hj : j < n := by rw [S.idxAt_block h] at hc; omega
      have hE : S.slotAt (nbr c HexDir.E) = .block (j + 1) := by
        rw [S.slotAt_nbr_E]
        exact S.step_of_block_lt h hj
      rw [S.dirAt_block h, show (HexDir.W).opp = HexDir.E from by decide, S.dirAt_block hE]
    | gapL =>
      have hs : S.subOf c < n := by rw [S.idxAt_gapL h] at hc; omega
      rw [S.dirAt_gapL h, show (HexDir.SE).opp = HexDir.NW from by decide,
        S.dirAt_gapL (by rw [S.slotAt_nbr_NW hs, h])]
    | gapR =>
      have hs : 0 < S.subOf c := by rw [S.idxAt_gapR h] at hc; omega
      rw [S.dirAt_gapR h, show (HexDir.NW).opp = HexDir.SE from by decide,
        S.dirAt_gapR (by rw [S.slotAt_nbr_SE hs, h])]
  pred_idx c hc := by
    have h0 := S.subOf_nonneg c
    have hn := S.subOf_le c
    cases h : S.slotAt c with
    | block j =>
      have hjn := S.block_le (r := S.bandOf c) (x := shearCol c) h
      have hj : j < n := by rw [S.idxAt_block h] at hc; omega
      have hE : S.slotAt (nbr c HexDir.E) = .block (j + 1) := by
        rw [S.slotAt_nbr_E]
        exact S.step_of_block_lt h hj
      rw [S.dirAt_block h, show (HexDir.W).opp = HexDir.E from by decide, S.idxAt_block hE,
        S.idxAt_block h]
      omega
    | gapL =>
      have hs : S.subOf c < n := by rw [S.idxAt_gapL h] at hc; omega
      have hNW : S.slotAt (nbr c HexDir.NW) = .gapL := by rw [S.slotAt_nbr_NW hs, h]
      rw [S.dirAt_gapL h, show (HexDir.SE).opp = HexDir.NW from by decide, S.idxAt_gapL hNW,
        S.idxAt_gapL h, S.subOf_nbr_NW hs]
      omega
    | gapR =>
      have hs : 0 < S.subOf c := by rw [S.idxAt_gapR h] at hc; omega
      have hSE : S.slotAt (nbr c HexDir.SE) = .gapR := by rw [S.slotAt_nbr_SE hs, h]
      rw [S.dirAt_gapR h, show (HexDir.NW).opp = HexDir.SE from by decide, S.idxAt_gapR hSE,
        S.idxAt_gapR h, S.subOf_nbr_SE hs]
      omega

@[simp] lemma toTiling_dir (c : Hex) : S.toTiling.dir c = S.dirAt c := rfl
@[simp] lemma toTiling_idx (c : Hex) : S.toTiling.idx c = S.idxAt c := rfl

end Schematic

end StickPolyhex
