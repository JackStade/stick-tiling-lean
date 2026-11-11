import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# The hexagonal grid

This file sets up the combinatorial model of the hexagonal grid that is used to formalise
tilings by *stick* polyhexes (see `Tiling/Proofs/StickTiling.lean`).

The hexagons we use have two vertical edges (on the left and on the right), so every hexagon
has six neighbours, in the directions `E`, `NE`, `NW`, `W`, `SW`, `SE`.  Cells are recorded in
*axial coordinates*: the cell `(p, q)` is the cell reached from the origin by `p` steps east
and `q` steps north-east.

Directions are modelled by `ZMod 6`, so that adding `1` to a direction is a rotation by `60°`
and adding `3` is a rotation by `180°` (i.e. taking the opposite direction).
-/

namespace StickPolyhex

/-- A cell of the hexagonal grid, in axial coordinates:
`(p, q)` is `p` steps east and `q` steps north-east of the origin. -/
abbrev Hex : Type := ℤ × ℤ

/-- A direction in the hexagonal grid.  It is modelled by `ZMod 6`: adding `1` rotates by
`60°` counterclockwise, so adding `3` gives the opposite direction. -/
abbrev HexDir : Type := ZMod 6

namespace HexDir

/-- The eastward direction. -/
def E : HexDir := 0
/-- The north-east direction. -/
def NE : HexDir := 1
/-- The north-west direction. -/
def NW : HexDir := 2
/-- The westward direction. -/
def W : HexDir := 3
/-- The south-west direction. -/
def SW : HexDir := 4
/-- The south-east direction. -/
def SE : HexDir := 5

/-- The translation vector, in axial coordinates, corresponding to a direction. -/
def vec (d : HexDir) : Hex :=
  ![(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)] d

/-- The direction opposite to `d`, i.e. `d` rotated by `180°`. -/
def opp (d : HexDir) : HexDir := d + 3

@[simp] lemma opp_opp (d : HexDir) : d.opp.opp = d := by
  revert d; decide

@[simp] lemma vec_opp (d : HexDir) : d.opp.vec = -d.vec := by
  revert d; decide

lemma vec_ne_zero (d : HexDir) : d.vec ≠ 0 := by
  revert d; decide

/-- Two directions with the same translation vector are equal. -/
lemma vec_injective : Function.Injective vec := by decide

/-- There are exactly six directions. -/
lemma cases_six (f : HexDir) : f = E ∨ f = NE ∨ f = NW ∨ f = W ∨ f = SW ∨ f = SE := by
  revert f; decide

@[simp] lemma E_ne_W : E ≠ W := by decide
@[simp] lemma W_ne_E : W ≠ E := by decide
@[simp] lemma NE_ne_E : NE ≠ E := by decide
@[simp] lemma NE_ne_W : NE ≠ W := by decide
@[simp] lemma NW_ne_E : NW ≠ E := by decide
@[simp] lemma NW_ne_W : NW ≠ W := by decide
@[simp] lemma SW_ne_E : SW ≠ E := by decide
@[simp] lemma SW_ne_W : SW ≠ W := by decide
@[simp] lemma SE_ne_E : SE ≠ E := by decide
@[simp] lemma SE_ne_W : SE ≠ W := by decide

end HexDir

/-- The neighbour of the cell `c` in direction `d`. -/
def nbr (c : Hex) (d : HexDir) : Hex := c + d.vec

@[simp] lemma nbr_opp_nbr (c : Hex) (d : HexDir) : nbr (nbr c d) d.opp = c := by
  simp [nbr, add_assoc]

@[simp] lemma nbr_nbr_opp (c : Hex) (d : HexDir) : nbr (nbr c d.opp) d = c := by
  simp [nbr, add_assoc]

lemma nbr_ne_self (c : Hex) (d : HexDir) : nbr c d ≠ c := by
  simp [nbr, HexDir.vec_ne_zero d]

end StickPolyhex
