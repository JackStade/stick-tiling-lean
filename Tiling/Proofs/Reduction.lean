import Tiling.Proofs.ABSpecEquiv
import Tiling.Proofs.ABMain

/-!
# From Wang tile sets to marked sticks

This file assembles the reduction: to a Wang tile set `T` it attaches the marked stick prototile
`reduceStick T`, an instance of the grid stick tiling problem `StickTilesGrid`.

The construction is the composition of

* `Tiling.AB.reduceAB`, the reduction of Section 2.2 from Wang tiling to AB tiling;
* `ABSim.abSpecData`, the bucket data of Sections 2.6–2.8 in finite form; and
* `GapSpecData.markData`, the marks of Section 2.5 placed on a block.

A Wang tile set which does not tile at all — the empty one — is sent to the unsatisfiable
specification `ABSim.emptySpecData`.

`ABSim.stickTilesGrid_of_tilesPlane` is the easy direction of the correctness of the reduction:
if the Wang tile set tiles the plane, then the marked stick tiles the hexagonal grid.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB LeanWang

/-- The finite specification with one bucket, one value and no allowed value: it describes
`ABSim.emptyGapSpec`, which no gap assignment satisfies. -/
def emptySpecData : GapSpecData where
  sRaw := 1
  vRaw := 1
  Lraw := []
  Rraw := []
  IloRaw := []
  IhiRaw := []

lemma emptySpecData_ilo (k : ℕ) : emptySpecData.ilo k = 1 := by
  simp only [GapSpecData.ilo, GapSpecData.v, emptySpecData]
  norm_num

lemma emptySpecData_ihi (k : ℕ) : emptySpecData.ihi k = 1 := by
  simp only [GapSpecData.ihi, GapSpecData.ilo, GapSpecData.v, emptySpecData]
  norm_num

lemma emptySpecData_toGapSpec : emptySpecData.toGapSpec = emptyGapSpec := by
  have hv : emptySpecData.v = 1 := rfl
  have hs : emptySpecData.s = 1 := rfl
  refine GapSpec.ext' hs hv ?_ ?_ ?_ ?_
  · funext k
    ext x
    simp only [GapSpecData.toGapSpec_L, Set.mem_setOf_eq, GapSpecData.mem_Lval, emptySpecData]
    simp [emptyGapSpec]
  · funext k
    ext x
    simp only [GapSpecData.toGapSpec_R, Set.mem_setOf_eq, GapSpecData.mem_Rval, emptySpecData]
    simp [emptyGapSpec]
  · funext k
    show ((emptySpecData.ilo k : ℕ) : ℤ) - (emptySpecData.v : ℤ) = 0
    rw [emptySpecData_ilo k, hv]
    norm_num
  · funext k
    show ((emptySpecData.ihi k : ℕ) : ℤ) - (emptySpecData.v : ℤ) = 0
    rw [emptySpecData_ihi k, hv]
    norm_num

/-- The finite bucket data attached to a Wang tile set. -/
def reduceSpecData (T : TileSet) : GapSpecData :=
  if T = [] then emptySpecData else abSpecData (reduceAB T)

/-- **The reduction.**  The marked stick prototile attached to a Wang tile set: an instance of
the grid stick tiling problem. -/
def reduceStick (T : TileSet) : MarkData := (reduceSpecData T).markData

lemma reduceStick_rules (T : TileSet) :
    (reduceStick T).rules =
      markedRules (reduceSpecData T).toGapSpec.blockLen (reduceSpecData T).toGapSpec.marking :=
  GapSpecData.markData_rules _

lemma tileSet_ne_nil_of_tilesPlane {T : TileSet} (h : TilesPlane T) : T ≠ [] := by
  rintro rfl
  obtain ⟨x, -⟩ := h
  exact List.not_mem_nil (x (0, 0)).2

lemma reduceAB_A_ne_nil {T : TileSet} (h : T ≠ []) : (reduceAB T).A ≠ [] := by
  simp only [reduceAB, ne_eq, List.map_eq_nil_iff]
  exact h

lemma reduceAB_B_ne_nil {T : TileSet} (h : T ≠ []) : (reduceAB T).B ≠ [] := by
  simp only [reduceAB, ne_eq, List.map_eq_nil_iff]
  exact h

/-- For a non-degenerate Wang tile set, the specification computed by the reduction is the
specification of Sections 2.6–2.8. -/
lemma reduceSpecData_toGapSpec {T : TileSet} (h : T ≠ []) :
    (reduceSpecData T).toGapSpec = (abData (reduceAB T) (reduceAB_A_ne_nil h)).spec := by
  rw [reduceSpecData, if_neg h]
  exact abSpecData_toGapSpec _ _

/-- A gap assignment for the computed specification gives a tiling of the hexagonal grid by the
computed marked stick. -/
lemma stickTilesGrid_of_gapAssignment {T : TileSet}
    (A : GapAssignment (reduceSpecData T).toGapSpec) : StickTilesGrid (reduceStick T) := by
  obtain ⟨W, hW, -⟩ := GapSpec.exists_tiling_of_gapAssignment A
  refine ⟨W, ?_⟩
  rw [reduceStick_rules]
  exact hW

/-- **The easy direction of the reduction.**  If a Wang tile set tiles the plane, the marked
stick prototile computed from it tiles the hexagonal grid subject to its matching rules. -/
theorem stickTilesGrid_of_tilesPlane {T : TileSet} (h : TilesPlane T) :
    StickTilesGrid (reduceStick T) := by
  have hne := tileSet_ne_nil_of_tilesPlane h
  have hA := reduceAB_A_ne_nil hne
  have hB := reduceAB_B_ne_nil hne
  have hab : ABTilesPlane (reduceAB T) := (tilesPlane_iff_abTilesPlane T).1 h
  obtain ⟨W⟩ := (nonempty_indexTiling_iff_abTilesPlane hA hB).2 hab
  have hga : Nonempty (GapAssignment (abData (reduceAB T) hA).spec) :=
    nonempty_gapAssignment_of_indexTiling W
  rw [← reduceSpecData_toGapSpec hne] at hga
  exact stickTilesGrid_of_gapAssignment hga.some

end ABSim

end StickPolyhex
