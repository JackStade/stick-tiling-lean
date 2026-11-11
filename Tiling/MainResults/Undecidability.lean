import Tiling.MainResults.StickInstance
import Tiling.MainResults.Computability
import Tiling.Proofs.Undecidability

/-!
# Verified lower bounds for stick tiling

The decision problem is `StickTilesGrid` on finite `MarkData`: a single marked
stick tiles the hexagonal grid, with the specified base and marking rules.
These are unconditional theorems, using the verified Wang domino theorem.
The geometric, computability, and undecidability proofs are outside this folder.
-/

namespace Tiling.MainResults

open StickPolyhex

/-- No total algorithm decides whether the input marked stick tiles the hexagonal grid. -/
theorem stickTiling_undecidable : ¬ ComputablePred StickTilesGrid :=
  StickPolyhex.ABSim.stickTilesGrid_undecidable

/-- Every co-r.e. predicate computably many-one reduces to stick tiling. -/
theorem stickTiling_coREHard : LeanWang.CoREHard StickTilesGrid :=
  StickPolyhex.ABSim.stickTilesGrid_coREHard

end Tiling.MainResults
