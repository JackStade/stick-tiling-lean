import Tiling.Proofs.Reduction
import Tiling.Proofs.GapIndex
import Tiling.Proofs.Rotation
import Tiling.Proofs.Lemma4
import Tiling.Proofs.MarkedCorrespondence

/-!
# Correctness of the reduction: the converse direction

`ABSim.stickTilesGrid_of_tilesPlane` shows that a Wang tile set which tiles the plane is sent by
the reduction to a marked stick which tiles the hexagonal grid.  This file proves the converse,
and therefore the correctness of the reduction: `ABSim.stickTilesGrid_iff_tilesPlane`.

The argument runs through the whole development:

* Lemma 4 (`StickTiling.formsWeavePattern_of_satisfiesWeaveRules`): a tiling satisfying the
  matching rules forms a weave pattern for *some* orientation;
* `StickTiling.exists_isWeavePattern_W`: rotating it, one may assume the orientation is the
  reference one;
* `StickTiling.exists_schematic_respectsMarking`: such a tiling is described by a schematic
  respecting the marks;
* `Schematic.respectsMarking_iff_gapConditions`: that schematic satisfies the gap conditions;
* `Schematic.nonempty_gapAssignment_of_satisfiesGapConditions`: its gaps can be indexed
  coherently, giving a gap assignment;
* `Tiling.AB` and Sections 2.6–2.8: a gap assignment yields an AB tiling of the plane and
  hence a Wang tiling.
-/

namespace StickPolyhex

lemma GapSpec.four_le_blockLen (G : GapSpec) : 4 ≤ G.blockLen := by
  have hv := G.hv
  have hs := G.hs
  have hlb : 2 * G.v ≤ G.lb := Nat.le_add_left _ _
  have hmul : 1 * G.lb ≤ G.s * G.lb := Nat.mul_le_mul_right _ hs
  unfold GapSpec.blockLen
  omega

/-- **A tiling by the marked stick of a specification gives a gap assignment.**  This is the
converse of `GapSpec.exists_tiling_of_gapAssignment`. -/
theorem GapSpec.nonempty_gapAssignment_of_tiling {G : GapSpec}
    (W : StickTiling (G.blockLen + 1))
    (hW : W.SatisfiesRules (markedRules G.blockLen G.marking)) :
    Nonempty (GapAssignment G) := by
  have hn : 4 ≤ G.blockLen := G.four_le_blockLen
  have hweave : W.FormsWeavePattern :=
    W.formsWeavePattern_of_satisfiesWeaveRules
      (StickTiling.satisfiesWeaveRules_of_satisfiesRules hW) (by omega)
  obtain ⟨W', hW', hwp⟩ := W.exists_isWeavePattern_W hW hweave
  obtain ⟨S, -, -, hmark⟩ := W'.exists_schematic_respectsMarking G.marking hn hW' hwp
  exact Schematic.nonempty_gapAssignment_of_satisfiesGapConditions
    (Schematic.respectsMarking_iff_gapConditions.1 hmark)

namespace ABSim

open Tiling.AB LeanWang

/-- A tiling of the hexagonal grid by the marked stick computed from a Wang tile set gives a gap
assignment for the computed specification. -/
lemma nonempty_gapAssignment_of_stickTilesGrid {T : TileSet} (h : StickTilesGrid (reduceStick T)) :
    Nonempty (GapAssignment (reduceSpecData T).toGapSpec) := by
  obtain ⟨W, hW⟩ := h
  rw [reduceStick_rules] at hW
  exact GapSpec.nonempty_gapAssignment_of_tiling W hW

/-- **The converse direction of the reduction.**  If the marked stick prototile computed from a
Wang tile set tiles the hexagonal grid subject to its matching rules, then the Wang tile set
tiles the plane. -/
theorem tilesPlane_of_stickTilesGrid {T : TileSet} (h : StickTilesGrid (reduceStick T)) :
    TilesPlane T := by
  have hga := nonempty_gapAssignment_of_stickTilesGrid h
  by_cases hnil : T = []
  · exfalso
    rw [reduceSpecData, if_pos hnil, emptySpecData_toGapSpec] at hga
    exact not_nonempty_gapAssignment_emptyGapSpec hga
  · have hA := reduceAB_A_ne_nil hnil
    have hB := reduceAB_B_ne_nil hnil
    rw [reduceSpecData_toGapSpec hnil] at hga
    exact (tilesPlane_iff_abTilesPlane T).2
      ((nonempty_indexTiling_iff_abTilesPlane hA hB).1
        (nonempty_indexTiling_of_gapAssignment _ hga))

/-- **Correctness of the reduction.**  A Wang tile set tiles the plane if and only if the marked
stick prototile computed from it tiles the hexagonal grid subject to its edge-to-edge matching
rules. -/
theorem stickTilesGrid_iff_tilesPlane (T : TileSet) :
    StickTilesGrid (reduceStick T) ↔ TilesPlane T :=
  ⟨tilesPlane_of_stickTilesGrid, stickTilesGrid_of_tilesPlane⟩

end ABSim

end StickPolyhex
