import Tiling.Proofs.MarkedTiling
import Tiling.Proofs.SchematicOfTiling

/-!
# Valid tilings correspond to valid schematics

This file puts together the two halves of the correspondence between the tilings by the stick
prototile decorated according to a marking `M` of a block of length `n` and the schematics with
blocks of length `n` that respect `M`:

* `Schematic.toTiling_satisfiesRules_formsWeavePattern`: a schematic respecting the markings
  describes a weave-pattern tiling satisfying the marked rules (and distinct schematics describe
  distinct tilings, by `Schematic.toTiling_injective`);
* `StickTiling.exists_schematic_respectsMarking`: conversely a normalised weave-pattern tiling
  satisfying the marked rules is, up to a translation, described by a schematic respecting the
  markings.

Since Lemma 4 (`StickTiling.formsWeavePattern_of_satisfiesWeaveRules`) shows that every tiling
satisfying the rules forms a weave pattern, the only real restriction in the second statement is
the normalisation of the orientation.
-/

namespace StickPolyhex

namespace StickTiling

/-- Satisfying a set of edge-matching rules is invariant under translation. -/
lemma satisfiesRules_translate {N : ℕ} {T : StickTiling N} {R : EdgeRules N}
    (h : T.SatisfiesRules R) (v : Hex) : (T.translate v).SatisfiesRules R := by
  intro c e p q hp hq
  refine h (c + v) e p q hp ?_
  have hnbr : nbr c e + v = nbr (c + v) e := by
    simp only [nbr]; abel
  rw [← hnbr]
  exact hq

variable {n : ℕ} (T : StickTiling (n + 1)) (M : Marking n)

/-- **Every normalised weave-pattern tiling satisfying the marked rules is described by a
schematic respecting the markings**, up to a translation. -/
theorem exists_schematic_respectsMarking (hn : 4 ≤ n)
    (hv : T.SatisfiesRules (markedRules n M)) (hw : T.IsWeavePattern HexDir.W) :
    ∃ (S : Schematic n) (v : Hex), S.toTiling = T.translate v ∧ S.RespectsMarking M := by
  obtain ⟨S, v, hSv⟩ :=
    T.exists_schematic (StickTiling.satisfiesWeaveRules_of_satisfiesRules hv) hn hw
  refine ⟨S, v, hSv, S.respectsMarking_of_toTiling_satisfiesRules M ?_⟩
  rw [hSv]
  exact StickTiling.satisfiesRules_translate hv v

end StickTiling

namespace Schematic

variable {n : ℕ} (S : Schematic n) (M : Marking n)

/-- **A schematic respecting its markings describes a weave-pattern tiling satisfying the marked
rules.** -/
theorem toTiling_satisfiesRules_formsWeavePattern (hM : S.RespectsMarking M) :
    S.toTiling.SatisfiesRules (markedRules n M) ∧ S.toTiling.FormsWeavePattern :=
  ⟨S.toTiling_satisfiesRules_of_respectsMarking M hM, S.toTiling_formsWeavePattern⟩

end Schematic

end StickPolyhex
