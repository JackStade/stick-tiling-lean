import Tiling.Proofs.Lemma4
import Tiling.Proofs.SchematicWeave

/-!
# Weave-pattern tilings in sheared coordinates

This file starts the proof of the converse of the correspondence established in
`Tiling/Proofs/SchematicWeave.lean`: *every* tiling satisfying the weave rules is the tiling
described by a block schematic, up to a translation.

Throughout this development the orientation of the tiling is normalised: the horizontal sticks
point west, i.e. the tiling satisfies `StickTiling.IsWeavePattern HexDir.W`.  By Lemma 4 every
tiling satisfying the weave rules can be so oriented after a rotation.

The sheared coordinates `shearCol`, `shearRow` of `Tiling/Proofs/SchematicTiling.lean` are used
throughout: a horizontal stick (direction `W`) occupies consecutive columns of one row, and a
left-slanting stick (direction `NW` or `SE`) occupies consecutive rows of one column.  This file
collects

* the translation between the directions `HexDir.W + k` and the named directions;
* the behaviour of `shearCol`/`shearRow` along a stick;
* the fact that every cell of such a tiling is *anchored*
  (`StickTiling.anchored_all_of_isWeavePattern`), which gives, for every left-slanting stick,
  a horizontal cell of a left-leaning stack directly below its lower end and directly above its
  upper end.
-/

namespace StickPolyhex

namespace StickTiling

/-! ### The directions around `HexDir.W` -/

@[simp] lemma W_add_one : HexDir.W + 1 = HexDir.SW := by decide
@[simp] lemma W_add_two : HexDir.W + 2 = HexDir.SE := by decide
@[simp] lemma W_add_three : HexDir.W + 3 = HexDir.E := by decide
@[simp] lemma W_add_four : HexDir.W + 4 = HexDir.NE := by decide
@[simp] lemma W_add_five : HexDir.W + 5 = HexDir.NW := by decide

lemma W_opp : HexDir.W.opp = HexDir.E := by decide
lemma NW_opp : HexDir.NW.opp = HexDir.SE := by decide
lemma SE_opp : HexDir.SE.opp = HexDir.NW := by decide
lemma E_opp : HexDir.E.opp = HexDir.W := by decide

variable {n : ℕ} (T : StickTiling n)

/-! ### Sheared coordinates along a stick -/

@[simp] lemma shearCol_walk_W (c : Hex) (k : ℤ) :
    shearCol (walk c HexDir.W k) = shearCol c - k := by
  simp [shearCol, walk, HexDir.vec, HexDir.W]
  ring

@[simp] lemma shearRow_walk_W (c : Hex) (k : ℤ) :
    shearRow (walk c HexDir.W k) = shearRow c := by
  simp [shearRow, walk, HexDir.vec, HexDir.W]

@[simp] lemma shearCol_walk_NW (c : Hex) (k : ℤ) :
    shearCol (walk c HexDir.NW k) = shearCol c := by
  simp [shearCol, walk, HexDir.vec, HexDir.NW]
  ring

@[simp] lemma shearRow_walk_NW (c : Hex) (k : ℤ) :
    shearRow (walk c HexDir.NW k) = shearRow c + k := by
  simp [shearRow, walk, HexDir.vec, HexDir.NW]

@[simp] lemma shearCol_walk_SE (c : Hex) (k : ℤ) :
    shearCol (walk c HexDir.SE k) = shearCol c := by
  simp [shearCol, walk, HexDir.vec, HexDir.SE]
  ring

@[simp] lemma shearRow_walk_SE (c : Hex) (k : ℤ) :
    shearRow (walk c HexDir.SE k) = shearRow c - k := by
  simp [shearRow, walk, HexDir.vec, HexDir.SE]
  ring

/-- The head of a horizontal stick lies in the same row, `idx - 1` columns further east. -/
lemma shear_head_W {c : Hex} (h : T.dir c = HexDir.W) :
    shearCol (T.head c) = shearCol c + ((T.idx c : ℤ) - 1) ∧ shearRow (T.head c) = shearRow c := by
  rw [head, h]
  refine ⟨by simp; ring, by simp⟩

/-- The head of a stick of direction `NW` is its lowest cell. -/
lemma shear_head_NW {c : Hex} (h : T.dir c = HexDir.NW) :
    shearCol (T.head c) = shearCol c ∧ shearRow (T.head c) = shearRow c - ((T.idx c : ℤ) - 1) := by
  rw [head, h]
  refine ⟨by simp, by simp; ring⟩

/-- The head of a stick of direction `SE` is its highest cell. -/
lemma shear_head_SE {c : Hex} (h : T.dir c = HexDir.SE) :
    shearCol (T.head c) = shearCol c ∧ shearRow (T.head c) = shearRow c + ((T.idx c : ℤ) - 1) := by
  rw [head, h]
  refine ⟨by simp, by simp; ring⟩

lemma shear_tail_of_head {c : Hex} (hn : 0 < n) :
    T.tail c = walk (T.head c) (T.dir c) ((n : ℤ) - 1) := by
  rw [tail, cellOfStick]
  congr 1
  omega

/-- Two cells of the same stick with the same index are equal. -/
lemma eq_of_mem_stickOf_of_idx_eq {c x y : Hex} (hx : x ∈ T.stickOf c) (hy : y ∈ T.stickOf c)
    (h : T.idx x = T.idx y) : x = y := by
  rw [mem_stickOf_iff] at hx hy
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hy
  rw [T.cellOfStick_idx c k hk, T.cellOfStick_idx c l hl] at h
  congr 1
  omega

/-! ### Every cell of a normalised weave tiling is anchored -/

/-- In a tiling satisfying the weave rules which has a horizontal stick of a left-leaning stack,
every cell is anchored: it lies on a horizontal stick of a left-leaning stack, or on a
left-slanting stick resting on such a stack from above or from below. -/
theorem anchored_all (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) {u : HexDir} {c₀ : Hex}
    (hd₀ : T.dir c₀ = u) (hL₀ : T.IsLeftLeaningStack c₀) (z : Hex) : T.Anchored u z := by
  refine forall_of_nbr_closed (P := fun w => T.Anchored u w) (z₀ := c₀) (Or.inl ⟨hd₀, hL₀⟩)
    (fun w hw e => T.anchored_nbr hv hn hw e) z

end StickTiling

end StickPolyhex
