import Tiling.Proofs.ReductionCompute

/-!
# The standalone computable reduction from AB tiling to stick tiling

Both empty-list cases map to the unsatisfiable specification. For nonempty lists,
use the existing finite bucket construction, including its padding of unequal list lengths.
-/

namespace StickPolyhex.ABSim

open Tiling.AB

/-- Finite specification for an arbitrary AB instance, including degenerate inputs. -/
def reduceABSpecData (S : ABTileSet) : GapSpecData :=
  if S.A = [] ∨ S.B = [] then emptySpecData else abSpecData S

/-- The marked stick computed from an AB instance. -/
def reduceABStick (S : ABTileSet) : MarkData := (reduceABSpecData S).markData

private theorem specification_correct (S : ABTileSet) :
    Nonempty (GapAssignment (reduceABSpecData S).toGapSpec) ↔ ABTilesPlane S := by
  by_cases h : S.A = [] ∨ S.B = []
  · rw [reduceABSpecData, if_pos h, emptySpecData_toGapSpec]
    constructor
    · exact fun hga => False.elim (not_nonempty_gapAssignment_emptyGapSpec hga)
    · intro hab
      rcases h with hA | hB
      · exact False.elim (abTilesPlane_A_ne S hab hA)
      · exact False.elim (abTilesPlane_B_ne S hab hB)
  · have hA : S.A ≠ [] := fun ha => h (Or.inl ha)
    have hB : S.B ≠ [] := fun hb => h (Or.inr hb)
    rw [reduceABSpecData, if_neg h, abSpecData_toGapSpec S hA]
    constructor
    · intro hga
      exact (nonempty_indexTiling_iff_abTilesPlane hA hB).1
        (nonempty_indexTiling_of_gapAssignment _ hga)
    · intro hab
      obtain ⟨W⟩ := (nonempty_indexTiling_iff_abTilesPlane hA hB).2 hab
      exact nonempty_gapAssignment_of_indexTiling W

/-- Correctness for every AB instance. -/
theorem abTilesPlane_iff_stickTilesGrid (S : ABTileSet) :
    ABTilesPlane S ↔ StickTilesGrid (reduceABStick S) := by
  rw [← specification_correct S]
  constructor
  · rintro ⟨A⟩
    obtain ⟨W, hW, _⟩ := GapSpec.exists_tiling_of_gapAssignment A
    refine ⟨W, ?_⟩
    change W.SatisfiesRules (reduceABSpecData S).markData.rules
    rw [GapSpecData.markData_rules]
    exact hW
  · rintro ⟨W, hW⟩
    change W.SatisfiesRules (reduceABSpecData S).markData.rules at hW
    rw [GapSpecData.markData_rules] at hW
    exact GapSpec.nonempty_gapAssignment_of_tiling W hW

/-- Primitive recursiveness includes the two degenerate-input tests. -/
theorem reduceABStick_primrec : Primrec reduceABStick := by
  have ht : Primrec ABTileSet.equivProd := Primrec.of_equiv
  have hA : Primrec ABTileSet.A := Primrec.fst.comp ht
  have hB : Primrec ABTileSet.B := Primrec.snd.comp ht
  have he : PrimrecPred (fun S : ABTileSet => S.A = [] ∨ S.B = []) :=
    (Primrec.eq.comp hA (Primrec.const [])).or
      (Primrec.eq.comp hB (Primrec.const []))
  have hs : Primrec reduceABSpecData :=
    Primrec.ite he (Primrec.const emptySpecData) abSpecData_primrec
  exact GapSpecData.markData_primrec.comp hs

theorem reduceABStick_computable : Computable reduceABStick :=
  reduceABStick_primrec.to_comp

theorem ab_manyOneReducible_stickTilesGrid :
    ManyOneReducible ABTilesPlane StickTilesGrid :=
  ⟨reduceABStick, reduceABStick_computable, abTilesPlane_iff_stickTilesGrid⟩

end StickPolyhex.ABSim
