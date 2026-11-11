import Tiling.Proofs.GridStructure

/-!
# Lemma 4: every valid tiling forms a weave pattern

This file assembles the proof of Lemma 4 of the paper from the local analysis of a left-leaning
stack (`Tiling/Proofs/Weave.lean`, `Tiling/Proofs/StackTop.lean`,
`Tiling/Proofs/StackBottom.lean`, `Tiling/Proofs/StackFour.lean`), the covering of the plane
(`Tiling/Proofs/Coverage.lean`, `Tiling/Proofs/HoleStacks.lean`,
`Tiling/Proofs/HoleEnds.lean`, `Tiling/Proofs/StepStack.lean`,
`Tiling/Proofs/StepHole.lean`) and the structure of the grid of horizontal stacks
(`Tiling/Proofs/GridStructure.lean`).

The orientation `u` is the one produced by `StickTiling.exists_weaveCell_all`: the direction of
the sticks of some left-leaning stack, for which every cell of the plane is a weave cell.  The
nine conditions of `StickTiling.IsWeavePattern` are then verified one by one.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Lemma 4 -/

/-- **Lemma 4 of the paper.**  Every valid tiling of the plane by sticks of length at least `5`
forms a weave pattern. -/
theorem formsWeavePattern_of_satisfiesWeaveRules (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n) :
    T.FormsWeavePattern := by
  obtain ⟨u, ⟨c₀, hdc₀, hLc₀⟩, hcov⟩ := T.exists_weaveCell_all hv hn
  refine ⟨u, ?_⟩
  refine
    { horizontal_or_slantsLeft := ?_
      exists_horizontal := ⟨c₀, hdc₀⟩
      horizontal_leftLeaning := fun z hd => T.isLeftLeaningStack_of_weaveCell (hcov z) hd
      slantsLeft_rightLeaning := fun z hs => T.isRightLeaningStack_of_weaveCell (hcov z) hs
      horizontal_height := fun z hd => T.stackHeight_eq_of_isLeftLeaningStack hv (by omega)
        (T.isLeftLeaningStack_of_weaveCell (hcov z) hd)
      two_above_two_below := fun z hd => T.two_above_two_below_of_weaveCell hv hn hcov hd
      overlap := fun z z' hd hd' hab => T.overlap_of_weaveCell hv hn hcov hd hd' hab
      grid_cell := fun z a₁ a₂ hd hd₁ hd₂ h₁ h₂ hne =>
        T.grid_cell_of_weaveCell hv hn hcov hd hd₁ hd₂ h₁ h₂ hne
      no_back_to_back := fun v v' hdv hst => T.no_back_to_back_of_satisfiesWeaveRules hv (by omega) u hdv hst }
  · intro z
    rcases hcov z with ⟨hd, -⟩ | ⟨hs, -⟩
    · exact Or.inl hd
    · exact Or.inr hs

end StickTiling

end StickPolyhex
