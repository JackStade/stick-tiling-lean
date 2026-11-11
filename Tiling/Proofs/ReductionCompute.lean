import Tiling.Proofs.Reduction
import Tiling.Proofs.ReductionConverse
import Tiling.Proofs.ABCompute

/-!
# The reduction is computable

`ABSim.reduceStick` attaches a marked stick prototile to every Wang tile set.  This file proves
that it is computed by a primitive recursive — in particular computable — function
(`ABSim.reduceStick_primrec`, `ABSim.reduceStick_computable`): the whole construction of the
paper, from a Wang tile set to the decorated stick, is effective.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB LeanWang Primrec

theorem reduceAB_primrec : Primrec reduceAB := by
  have hg : Primrec (fun T : TileSet => (T.map toA, T.map toB)) :=
    Primrec.pair (Primrec.list_map Primrec.id (toA_primrec.comp Primrec.snd))
      (Primrec.list_map Primrec.id (toB_primrec.comp Primrec.snd))
  have h := (Primrec.of_equiv_symm_iff (e := ABTileSet.equivProd)
    (f := fun T : TileSet => (T.map toA, T.map toB))).2 hg
  exact h.of_eq fun _ => rfl

theorem reduceSpecData_primrec : Primrec reduceSpecData := by
  have h : Primrec (fun T : TileSet =>
      if T = [] then emptySpecData else abSpecData (reduceAB T)) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const []))
      (Primrec.const emptySpecData) (abSpecData_primrec.comp reduceAB_primrec)
  exact h.of_eq fun _ => rfl

/-- **The reduction is primitive recursive.**  The marked stick prototile attached to a Wang tile
set is computed from it by a primitive recursive function. -/
theorem reduceStick_primrec : Primrec reduceStick :=
  (GapSpecData.markData_primrec.comp reduceSpecData_primrec).of_eq fun _ => rfl

/-- **The reduction is computable.** -/
theorem reduceStick_computable : Computable reduceStick :=
  reduceStick_primrec.to_comp

/-- **Wang tiling is many-one reducible to the grid stick tiling problem with edge-to-edge
matching rules.**  The reduction is the computable map `reduceStick`, and a Wang tile set tiles
the plane exactly when the marked stick prototile computed from it tiles the hexagonal grid
subject to its matching rules. -/
theorem wang_manyOneReducible_stickTilesGrid : ManyOneReducible TilesPlane StickTilesGrid :=
  ⟨reduceStick, reduceStick_computable, fun T => (stickTilesGrid_iff_tilesPlane T).symm⟩

end ABSim

end StickPolyhex
