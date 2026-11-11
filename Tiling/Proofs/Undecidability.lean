import Tiling.Proofs.ReductionCompute
import LeanWang.Final

/-!
# Undecidability of the grid stick tiling problem

`ABSim.wang_manyOneReducible_stickTilesGrid` is a computable many-one reduction of the Wang
domino problem `LeanWang.TilesPlane` to the grid stick tiling problem `StickTilesGrid`.  This
file draws the computability-theoretic consequences of that reduction, which is the content of
the theorem of the paper's subsection "Final verification":

* `ABSim.not_computablePred_stickTilesGrid`: if the Wang domino problem is undecidable, then so
  is the problem of deciding whether a stick prototile with edge-to-edge matching rules tiles the
  hexagonal grid;
* `ABSim.coREHard_stickTilesGrid`: the same transfer for co-r.e. hardness;
* `ABSim.stickTilesGrid_undecidable` (also exported as `ABSim.theorem2`): the unconditional
  undecidability theorem, obtained by applying the reduction to `lean-wang`'s verified Robinson
  certificate;
* `ABSim.stickTilesGrid_coREHard`: the corresponding unconditional co-r.e.-hardness result.
-/

namespace StickPolyhex

namespace ABSim

open LeanWang

/-- **Undecidability transfers along the reduction.**  If no algorithm decides whether a Wang
tile set tiles the plane, then no algorithm decides whether a stick prototile with edge-to-edge
matching rules tiles the hexagonal grid. -/
theorem not_computablePred_stickTilesGrid (h : ¬ ComputablePred TilesPlane) :
    ¬ ComputablePred StickTilesGrid := fun hc =>
  h (ComputablePred.computable_of_manyOneReducible wang_manyOneReducible_stickTilesGrid hc)

/-- **Co-r.e. hardness transfers along the reduction.** -/
theorem coREHard_stickTilesGrid (h : CoREHard TilesPlane) : CoREHard StickTilesGrid :=
  fun p hp => (h p hp).trans wang_manyOneReducible_stickTilesGrid

/-- **Undecidability of monotiling with edge-to-edge matching rules.**  Given any certificate
reducing the fixed-input nonhalting problem to the Wang domino problem — that is, given the
classical undecidability of the domino problem — deciding whether a single stick prototile with
edge-to-edge matching rules tiles the hexagonal grid is undecidable. -/
theorem stickTilesGrid_undecidable_of_dominoReduction (r : DominoProblem.Reduction) :
    ¬ ComputablePred StickTilesGrid :=
  not_computablePred_stickTilesGrid r.undecidable

/-- With the same certificate, the grid stick tiling problem is co-r.e.-hard. -/
theorem stickTilesGrid_coREHard_of_dominoReduction (r : DominoProblem.Reduction) :
    CoREHard StickTilesGrid :=
  coREHard_stickTilesGrid r.coREHard

/-- **Undecidability of monotiling with edge-to-edge matching rules (Theorem 2).**  There is no
algorithm deciding whether the finite description of a single marked stick prototile produced
by this construction tiles the hexagonal grid subject to its edge-to-edge matching rules.

This is an unconditional theorem: `LeanWang.domino_problem_undecidable` is supplied by the
verified Robinson reduction in `lean-wang`. -/
theorem stickTilesGrid_undecidable : ¬ ComputablePred StickTilesGrid :=
  not_computablePred_stickTilesGrid LeanWang.domino_problem_undecidable

/-- The formal statement corresponding to Theorem 2 of *Two Tiling is Undecidable*. -/
theorem theorem2 : ¬ ComputablePred StickTilesGrid :=
  stickTilesGrid_undecidable

/-- The grid stick tiling problem is in fact co-r.e.-hard. -/
theorem stickTilesGrid_coREHard : CoREHard StickTilesGrid :=
  coREHard_stickTilesGrid LeanWang.domino_problem_coRE_hard

end ABSim

end StickPolyhex
