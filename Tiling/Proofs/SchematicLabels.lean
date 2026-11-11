import Tiling.Proofs.SchematicTiling
import Tiling.Proofs.EdgeRules

/-!
# The edge labels of the tiling described by a schematic

This file computes the label (in the sense of `Tiling/Proofs/MatchingRules.lean`) carried by
each edge of the tiling `S.toTiling` of a schematic `S` with blocks of length `n`.

Cells are addressed by `cellAt n r x s`, the cell in the column `x` of the band `r` at height
`s` inside that band (`0 ≤ s ≤ n`); every cell is of this form, and the three "forward"
neighbours are

* `nbr (cellAt n r x s) HexDir.E  = cellAt n r (x+1) s`,
* `nbr (cellAt n r x s) HexDir.NW = cellAt n r x (s+1)`,
* `nbr (cellAt n r x s) HexDir.NE = cellAt n r (x+1) (s+1)`,

where `cellAt n r x (n+1) = cellAt n (r+1) x 0`.

The eighteen lemmas `label_block_*`, `label_gapL_*`, `label_gapR_*` give the label of each of
the six edges of a cell, according to the slot of its column and its height in the band.  With
`N = n + 1` the length of the sticks, they read (writing `j` for the index of a block column and
`s` for the height in the band):

| edge | `block j`            | `gapL`, height `s`   | `gapR`, height `s`     |
| ---- | -------------------- | -------------------- | ---------------------- |
| `E`  | `y₁` if `j = n`      | `z₂` if `s=0`, `d s` | `z₁` if `s=0`, `b s`   |
| `NE` | `z₁`/`b (n-j)`       | `x₁` if `s=n`, `c (s+1)` | `x₂` if `s=n`, `a (s+1)` |
| `NW` | `x₂`/`a (n+1-j)`     | `y₁` if `s = n`      | `y₂` if `s = n`        |
| `W`  | `y₂` if `j = 0`      | `z₁` if `s=n`, `b (n-s)` | `z₂` if `s=n`, `d (n-s)` |
| `SW` | `z₂`/`d j`           | `x₂` if `s=0`, `a (n+1-s)` | `x₁` if `s=0`, `c (n+1-s)` |
| `SE` | `x₁`/`c (j+1)`       | `y₂` if `s = 0`      | `y₁` if `s = 0`        |

(An empty entry means that the edge is interior to a stick, i.e. unlabelled.)
-/

namespace StickPolyhex

/-! ### Addressing cells by band, column and height -/

/-- The cell in the column `x` of the band `r`, at height `s` inside the band. -/
def cellAt (n : ℕ) (r x s : ℤ) : Hex := shearCell x (((n : ℤ) + 1) * r + s)

@[simp] lemma shearCol_cellAt (n : ℕ) (r x s : ℤ) : shearCol (cellAt n r x s) = x := by
  simp [cellAt]

@[simp] lemma shearRow_cellAt (n : ℕ) (r x s : ℤ) :
    shearRow (cellAt n r x s) = ((n : ℤ) + 1) * r + s := rfl

/-- Every cell is the cell at its column, band and height. -/
lemma cellAt_bandOf (n : ℕ) (c : Hex) :
    cellAt n (bandRow n (shearRow c)) (shearCol c) (subRow n (shearRow c)) = c := by
  refine hex_ext ?_ ?_
  · simp
  · simpa using bandRow_mul_add n (shearRow c)

/-- Climbing out of the top of a band enters the next band. -/
lemma cellAt_top (n : ℕ) (r x : ℤ) : cellAt n r x ((n : ℤ) + 1) = cellAt n (r + 1) x 0 := by
  refine hex_ext ?_ ?_ <;> simp
  ring

/-- Climbing out of the top of a band enters the next band; the version with the heights
written as natural numbers. -/
lemma cellAt_top_nat (n : ℕ) (r x : ℤ) :
    cellAt n r x (((n : ℕ) : ℤ) + 1) = cellAt n (r + 1) x ((0 : ℕ) : ℤ) := by
  refine hex_ext ?_ ?_ <;> simp
  ring

@[simp] lemma nbr_cellAt_E (n : ℕ) (r x s : ℤ) :
    nbr (cellAt n r x s) HexDir.E = cellAt n r (x + 1) s := by
  refine hex_ext ?_ ?_ <;> simp

@[simp] lemma nbr_cellAt_W (n : ℕ) (r x s : ℤ) :
    nbr (cellAt n r x s) HexDir.W = cellAt n r (x - 1) s := by
  refine hex_ext ?_ ?_ <;> simp

@[simp] lemma nbr_cellAt_NW (n : ℕ) (r x s : ℤ) :
    nbr (cellAt n r x s) HexDir.NW = cellAt n r x (s + 1) := by
  refine hex_ext ?_ ?_ <;> simp
  ring

@[simp] lemma nbr_cellAt_NE (n : ℕ) (r x s : ℤ) :
    nbr (cellAt n r x s) HexDir.NE = cellAt n r (x + 1) (s + 1) := by
  refine hex_ext ?_ ?_ <;> simp
  ring

@[simp] lemma nbr_cellAt_SE (n : ℕ) (r x s : ℤ) :
    nbr (cellAt n r x s) HexDir.SE = cellAt n r x (s - 1) := by
  refine hex_ext ?_ ?_ <;> simp
  ring

@[simp] lemma nbr_cellAt_SW (n : ℕ) (r x s : ℤ) :
    nbr (cellAt n r x s) HexDir.SW = cellAt n r (x - 1) (s - 1) := by
  refine hex_ext ?_ ?_ <;> simp
  ring

namespace Schematic

variable {n : ℕ} (S : Schematic n)

lemma bandOf_cellAt {r x s : ℤ} (h0 : 0 ≤ s) (hs : s ≤ n) :
    S.bandOf (cellAt n r x s) = r := by
  rw [bandOf, shearRow_cellAt]; exact bandRow_eq n r s h0 hs

lemma subOf_cellAt {r x s : ℤ} (h0 : 0 ≤ s) (hs : s ≤ n) :
    S.subOf (cellAt n r x s) = s := by
  rw [subOf, shearRow_cellAt]; exact subRow_eq n r s h0 hs

lemma slotAt_cellAt {r x s : ℤ} (h0 : 0 ≤ s) (hs : s ≤ n) :
    S.slotAt (cellAt n r x s) = S.slot r x := by
  rw [slotAt, S.bandOf_cellAt h0 hs, shearCol_cellAt]

/-! ### The labels of the six edges of a cell -/

section Labels

variable {r x : ℤ} {s : ℕ}

/-- The label of an edge of the tiling of a schematic, in terms of the slot and the height of
the cell. -/
lemma label_eq (c : Hex) (e : HexDir) :
    S.toTiling.label c e = frameLabel (n + 1) (S.idxAt c) (e - S.dirAt c + HexDir.W) := rfl

variable (hs : s ≤ n) {j : ℕ} (hb : S.slot r x = .block j)
include hs hb

private lemma idxAt_blockAt : S.idxAt (cellAt n r x s) = n + 1 - j := by
  rw [S.idxAt_block (by rw [S.slotAt_cellAt (by positivity) (by exact_mod_cast hs)]; exact hb)]

private lemma dirAt_blockAt : S.dirAt (cellAt n r x s) = HexDir.W :=
  S.dirAt_block (by rw [S.slotAt_cellAt (by positivity) (by exact_mod_cast hs)]; exact hb)

private lemma label_block (e : HexDir) :
    S.toTiling.label (cellAt n r x s) e = frameLabel (n + 1) (n + 1 - j) e := by
  rw [label_eq, S.idxAt_blockAt hs hb, S.dirAt_blockAt hs hb]
  congr 1
  simp [HexDir.W]

lemma label_block_E :
    S.toTiling.label (cellAt n r x s) HexDir.E = if j = n then some .y1 else none := by
  have hj : j ≤ n := S.block_le hb
  rw [S.label_block hs hb, frameLabel_E]
  by_cases h : j = n <;> simp [h]
  omega

lemma label_block_W :
    S.toTiling.label (cellAt n r x s) HexDir.W = if j = 0 then some .y2 else none := by
  have hj : j ≤ n := S.block_le hb
  rw [S.label_block hs hb, frameLabel_W]
  by_cases h : j = 0 <;> simp [h]
  omega

lemma label_block_NE :
    S.toTiling.label (cellAt n r x s) HexDir.NE =
      if j = n then some .z1 else some (.b (n - j)) := by
  have hj : j ≤ n := S.block_le hb
  rw [S.label_block hs hb, frameLabel_NE]
  by_cases h : j = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 - j - 1 = n - j by omega]

lemma label_block_NW :
    S.toTiling.label (cellAt n r x s) HexDir.NW =
      if j = 0 then some .x2 else some (.a (n + 1 - j)) := by
  have hj : j ≤ n := S.block_le hb
  rw [S.label_block hs hb, frameLabel_NW]
  by_cases h : j = 0 <;> simp [h]
  omega

lemma label_block_SW :
    S.toTiling.label (cellAt n r x s) HexDir.SW =
      if j = 0 then some .z2 else some (.d j) := by
  have hj : j ≤ n := S.block_le hb
  rw [S.label_block hs hb, frameLabel_SW]
  by_cases h : j = 0
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 - (n + 1 - j) = j by omega]

lemma label_block_SE :
    S.toTiling.label (cellAt n r x s) HexDir.SE =
      if j = n then some .x1 else some (.c (j + 1)) := by
  have hj : j ≤ n := S.block_le hb
  rw [S.label_block hs hb, frameLabel_SE]
  by_cases h : j = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 + 1 - (n + 1 - j) = j + 1 by omega]

end Labels

section LabelsGapL

variable {r x : ℤ} {s : ℕ} (hs : s ≤ n) (hb : S.slot r x = .gapL)
include hs hb

private lemma idxAt_gapLAt : S.idxAt (cellAt n r x s) = n + 1 - s := by
  rw [S.idxAt_gapL (by rw [S.slotAt_cellAt (by positivity) (by exact_mod_cast hs)]; exact hb),
    S.subOf_cellAt (by positivity) (by exact_mod_cast hs)]
  omega

private lemma dirAt_gapLAt : S.dirAt (cellAt n r x s) = HexDir.SE :=
  S.dirAt_gapL (by rw [S.slotAt_cellAt (by positivity) (by exact_mod_cast hs)]; exact hb)

private lemma label_gapL (e : HexDir) :
    S.toTiling.label (cellAt n r x s) e =
      frameLabel (n + 1) (n + 1 - s) (e - HexDir.SE + HexDir.W) := by
  rw [label_eq, S.idxAt_gapLAt hs hb, S.dirAt_gapLAt hs hb]

lemma label_gapL_NW :
    S.toTiling.label (cellAt n r x s) HexDir.NW = if s = n then some .y1 else none := by
  rw [S.label_gapL hs hb,
    show (HexDir.NW - HexDir.SE + HexDir.W : HexDir) = HexDir.E by decide, frameLabel_E]
  by_cases h : s = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

lemma label_gapL_SE :
    S.toTiling.label (cellAt n r x s) HexDir.SE = if s = 0 then some .y2 else none := by
  rw [S.label_gapL hs hb,
    show (HexDir.SE - HexDir.SE + HexDir.W : HexDir) = HexDir.W by decide, frameLabel_W]
  by_cases h : s = 0
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

lemma label_gapL_W :
    S.toTiling.label (cellAt n r x s) HexDir.W =
      if s = n then some .z1 else some (.b (n - s)) := by
  rw [S.label_gapL hs hb,
    show (HexDir.W - HexDir.SE + HexDir.W : HexDir) = HexDir.NE by decide, frameLabel_NE]
  by_cases h : s = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 - s - 1 = n - s by omega]

lemma label_gapL_SW :
    S.toTiling.label (cellAt n r x s) HexDir.SW =
      if s = 0 then some .x2 else some (.a (n + 1 - s)) := by
  rw [S.label_gapL hs hb,
    show (HexDir.SW - HexDir.SE + HexDir.W : HexDir) = HexDir.NW by decide, frameLabel_NW]
  by_cases h : s = 0
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

lemma label_gapL_E :
    S.toTiling.label (cellAt n r x s) HexDir.E =
      if s = 0 then some .z2 else some (.d s) := by
  rw [S.label_gapL hs hb,
    show (HexDir.E - HexDir.SE + HexDir.W : HexDir) = HexDir.SW by decide, frameLabel_SW]
  by_cases h : s = 0
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 - (n + 1 - s) = s by omega]

lemma label_gapL_NE :
    S.toTiling.label (cellAt n r x s) HexDir.NE =
      if s = n then some .x1 else some (.c (s + 1)) := by
  rw [S.label_gapL hs hb,
    show (HexDir.NE - HexDir.SE + HexDir.W : HexDir) = HexDir.SE by decide, frameLabel_SE]
  by_cases h : s = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 + 1 - (n + 1 - s) = s + 1 by omega]

end LabelsGapL

section LabelsGapR

variable {r x : ℤ} {s : ℕ} (hs : s ≤ n) (hb : S.slot r x = .gapR)
include hs hb

private lemma idxAt_gapRAt : S.idxAt (cellAt n r x s) = s + 1 := by
  rw [S.idxAt_gapR (by rw [S.slotAt_cellAt (by positivity) (by exact_mod_cast hs)]; exact hb),
    S.subOf_cellAt (by positivity) (by exact_mod_cast hs)]
  simp

private lemma dirAt_gapRAt : S.dirAt (cellAt n r x s) = HexDir.NW :=
  S.dirAt_gapR (by rw [S.slotAt_cellAt (by positivity) (by exact_mod_cast hs)]; exact hb)

private lemma label_gapR (e : HexDir) :
    S.toTiling.label (cellAt n r x s) e =
      frameLabel (n + 1) (s + 1) (e - HexDir.NW + HexDir.W) := by
  rw [label_eq, S.idxAt_gapRAt hs hb, S.dirAt_gapRAt hs hb]

lemma label_gapR_SE :
    S.toTiling.label (cellAt n r x s) HexDir.SE = if s = 0 then some .y1 else none := by
  rw [S.label_gapR hs hb,
    show (HexDir.SE - HexDir.NW + HexDir.W : HexDir) = HexDir.E by decide, frameLabel_E]
  by_cases h : s = 0
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

lemma label_gapR_NW :
    S.toTiling.label (cellAt n r x s) HexDir.NW = if s = n then some .y2 else none := by
  rw [S.label_gapR hs hb,
    show (HexDir.NW - HexDir.NW + HexDir.W : HexDir) = HexDir.W by decide, frameLabel_W]
  by_cases h : s = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

lemma label_gapR_E :
    S.toTiling.label (cellAt n r x s) HexDir.E =
      if s = 0 then some .z1 else some (.b s) := by
  rw [S.label_gapR hs hb,
    show (HexDir.E - HexDir.NW + HexDir.W : HexDir) = HexDir.NE by decide, frameLabel_NE]
  by_cases h : s = 0
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show s + 1 - 1 = s by omega]

lemma label_gapR_NE :
    S.toTiling.label (cellAt n r x s) HexDir.NE =
      if s = n then some .x2 else some (.a (s + 1)) := by
  rw [S.label_gapR hs hb,
    show (HexDir.NE - HexDir.NW + HexDir.W : HexDir) = HexDir.NW by decide, frameLabel_NW]
  by_cases h : s = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

lemma label_gapR_W :
    S.toTiling.label (cellAt n r x s) HexDir.W =
      if s = n then some .z2 else some (.d (n - s)) := by
  rw [S.label_gapR hs hb,
    show (HexDir.W - HexDir.NW + HexDir.W : HexDir) = HexDir.SW by decide, frameLabel_SW]
  by_cases h : s = n
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 - (s + 1) = n - s by omega]

lemma label_gapR_SW :
    S.toTiling.label (cellAt n r x s) HexDir.SW =
      if s = 0 then some .x1 else some (.c (n + 1 - s)) := by
  rw [S.label_gapR hs hb,
    show (HexDir.SW - HexDir.NW + HexDir.W : HexDir) = HexDir.SE by decide, frameLabel_SE]
  by_cases h : s = 0
  · simp [h]
  · rw [if_neg (by omega), if_neg h, show n + 1 + 1 - (s + 1) = n + 1 - s by omega]

end LabelsGapR

end Schematic

end StickPolyhex
