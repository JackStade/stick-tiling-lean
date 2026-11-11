import Tiling.Proofs.GapBackward

/-!
# The gap conditions characterise the valid schematics

This file records the main theorem of Section 2.5 of the paper, in the form asked for: given the
data `G : GapSpec` — the numbers `s` and `v`, the sets `R i`, `L i ⊆ {1, …, v}` and the intervals
`I i ⊆ {-v+1, …, v-1}` — the block length `G.blockLen` and the marks `G.marking` constructed in
`Tiling/Proofs/GapSpec.lean` are such that a schematic on blocks of that length is valid, i.e.
respects the marks, **if and only if** it satisfies the gap conditions
`Schematic.SatisfiesGapConditions`.

* `Schematic.respectsMarking_iff_gapConditions` is the statement for schematics;
* `Schematic.toTiling_satisfiesRules_iff_gapConditions` transfers it to the tilings themselves,
  through `Schematic.toTiling_satisfiesRules_iff`: the stick tiling described by a schematic
  satisfies the edge-matching rules decorated by the marks exactly when the schematic satisfies
  the gap conditions.
-/

namespace StickPolyhex

namespace Schematic

variable {G : GapSpec} {S : Schematic G.blockLen}

/-- **The gap conditions of Section 2.5.**  For the block length `G.blockLen` and the marks
`G.marking` built from the data `G` (the numbers `s` and `v`, the sets `R i`, `L i` and the
intervals `I i`), a schematic respects the marks if and only if it satisfies the gap
conditions. -/
theorem respectsMarking_iff_gapConditions :
    S.RespectsMarking G.marking ↔ S.SatisfiesGapConditions G :=
  ⟨gapConditions_of_respectsMarking, respectsMarking_of_gapConditions⟩

/-- The same statement for the tiling described by a schematic: it satisfies the edge-matching
rules of the paper decorated by the marks `G.marking` if and only if the schematic satisfies the
gap conditions. -/
theorem toTiling_satisfiesRules_iff_gapConditions :
    S.toTiling.SatisfiesRules (markedRules G.blockLen G.marking) ↔ S.SatisfiesGapConditions G :=
  (S.toTiling_satisfiesRules_iff G.marking).trans respectsMarking_iff_gapConditions

end Schematic

end StickPolyhex
