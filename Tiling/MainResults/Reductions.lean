import Tiling.MainResults.WangTiling
import Tiling.MainResults.ABTiling
import Tiling.MainResults.StickInstance
import Tiling.MainResults.Computability
import Tiling.Proofs.ABReduction

/-!
# Existence of the two computable reductions

These statements expose the input/output types, computability, and correctness
for every input. The constructions and technical proofs are imported from outside
this folder. Empty inputs are included; the AB lists need not have equal lengths.
-/

namespace Tiling.MainResults

open LeanWang Tiling.AB StickPolyhex

/-- Wang tiling computably reduces to AB tiling. -/
theorem exists_computable_wang_to_AB :
    ∃ f : TileSet → ABTileSet,
      Computable f ∧ ∀ T, TilesPlane T ↔ ABTilesPlane (f T) :=
  Tiling.AB.wang_manyOneReducible_abTiling

/-- AB tiling computably reduces to marked-stick tiling of the hexagonal grid. -/
theorem exists_computable_AB_to_stick :
    ∃ f : ABTileSet → MarkData,
      Computable f ∧ ∀ S, ABTilesPlane S ↔ StickTilesGrid (f S) :=
  StickPolyhex.ABSim.ab_manyOneReducible_stickTilesGrid

end Tiling.MainResults
