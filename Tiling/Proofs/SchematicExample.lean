import Tiling.Proofs.MarkedTiling
import Tiling.Proofs.SchematicWeave

/-!
# A periodic schematic

Schematics with blocks of length `n` exist as soon as `n ≥ 4` (which is also necessary, by
`Schematic.four_le`): `Schematic.periodic n hn` is the schematic all of whose gaps have one
column in their left part and one in their right part, each row being shifted three columns to
the right with respect to the row below.  Reading a row from left to right the pattern

`block 0, …, block n, gapL, gapR`

repeats with period `n + 3`.

Together with `Schematic.toTiling_satisfiesWeaveRules` this shows that the eleven matching rules
of the paper are satisfiable: `exists_satisfiesWeaveRules` exhibits a tiling of the plane by the
decorated stick of length `n + 1`.
-/

namespace StickPolyhex

namespace Schematic

/-- The slot of a column of the periodic schematic, according to the residue `m` of the column
modulo `n + 3`. -/
private def perSlot (n : ℕ) (m : ℤ) : Slot :=
  if m ≤ (n : ℤ) then .block m.toNat else if m = (n : ℤ) + 1 then .gapL else .gapR

/-- The periodic schematic with blocks of length `n`: all its gaps have a left part and a right
part of one column each, and each row is shifted three columns to the right with respect to the
row below. -/
def periodic (n : ℕ) (hn : 4 ≤ n) : Schematic n where
  slot r x := perSlot n ((x + 3 * r) % ((n : ℤ) + 3))
  slot_step r x := by
    have hp0 : (0 : ℤ) < (n : ℤ) + 3 := by positivity
    have h0 : 0 ≤ (x + 3 * r) % ((n : ℤ) + 3) := Int.emod_nonneg _ (by omega)
    have h1 : (x + 3 * r) % ((n : ℤ) + 3) < (n : ℤ) + 3 := Int.emod_lt_of_pos _ hp0
    have hnext : (x + 1 + 3 * r) % ((n : ℤ) + 3)
        = ((x + 3 * r) % ((n : ℤ) + 3) + 1) % ((n : ℤ) + 3) := by
      rw [Int.emod_add_emod, show x + 3 * r + 1 = x + 1 + 3 * r by ring]
    rw [hnext]
    by_cases hc : (x + 3 * r) % ((n : ℤ) + 3) + 1 < (n : ℤ) + 3
    · rw [Int.emod_eq_of_lt (by omega) hc]
      unfold perSlot
      split_ifs <;> simp only [Slot.Step] <;> omega
    · rw [show (x + 3 * r) % ((n : ℤ) + 3) + 1 = (n : ℤ) + 3 by omega, Int.emod_self]
      unfold perSlot
      split_ifs <;> simp only [Slot.Step] <;> omega
  slot_overlap r x := by
    have hp0 : (0 : ℤ) < (n : ℤ) + 3 := by positivity
    set m : ℤ := (x + 3 * r) % ((n : ℤ) + 3) with hmdef
    have h0 : 0 ≤ m := Int.emod_nonneg _ (by omega)
    have h1 : m < (n : ℤ) + 3 := Int.emod_lt_of_pos _ hp0
    have hnext : (x + 3 * (r + 1)) % ((n : ℤ) + 3) = (m + 3) % ((n : ℤ) + 3) := by
      rw [hmdef, Int.emod_add_emod, show x + 3 * r + 3 = x + 3 * (r + 1) by ring]
    intro hgap
    rw [hnext] at hgap
    by_cases hc : m + 3 < (n : ℤ) + 3
    · rw [Int.emod_eq_of_lt (by omega) hc] at hgap
      have hm1 : (n : ℤ) + 1 ≤ m + 3 := by
        by_contra hcon
        rw [perSlot, if_pos (by omega)] at hgap
        exact hgap
      exact ⟨m.toNat, by omega, by omega, by rw [perSlot, if_pos (by omega)]⟩
    · have he : (m + 3) % ((n : ℤ) + 3) = m - (n : ℤ) := by
        rw [show m + 3 = (m - (n : ℤ)) + ((n : ℤ) + 3) * 1 by ring, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [he, perSlot, if_pos (by omega)] at hgap
      exact hgap.elim

/-- The markings really constrain the tilings: the periodic schematic does not respect a marking
carrying a left-facing arrow on the top face at the position `n - 3`, since each of its gaps has
its left column directly above the column `n - 2` of a block of the row below. -/
theorem periodic_not_respectsMarking {n : ℕ} (hn : 4 ≤ n) (M : Marking n)
    (hM : n - 3 ∈ M.topArrowL) : ¬ (periodic n hn).RespectsMarking M := by
  intro hR
  have h1 : (periodic n hn).slot 0 ((n : ℤ) - 2) = .block (n - 3 + 1) := by
    show perSlot n (((n : ℤ) - 2 + 3 * 0) % ((n : ℤ) + 3)) = _
    rw [show ((n : ℤ) - 2 + 3 * 0) = (n : ℤ) - 2 by ring,
      Int.emod_eq_of_lt (by omega) (by omega), perSlot, if_pos (by omega)]
    congr 1
    omega
  have h2 : (periodic n hn).slot (0 + 1) ((n : ℤ) - 2) = .gapL := by
    show perSlot n (((n : ℤ) - 2 + 3 * (0 + 1)) % ((n : ℤ) + 3)) = _
    rw [show ((n : ℤ) - 2 + 3 * (0 + 1)) = (n : ℤ) + 1 by ring,
      Int.emod_eq_of_lt (by omega) (by omega), perSlot, if_neg (by omega), if_pos rfl]
  exact hR.topArrowL hM 0 ((n : ℤ) - 2) h1 h2

/-- The eleven matching rules of the paper are satisfiable: for every `n ≥ 4` there is a tiling
of the plane by the decorated stick of length `n + 1` satisfying them. -/
theorem exists_satisfiesWeaveRules {n : ℕ} (hn : 4 ≤ n) :
    ∃ T : StickTiling (n + 1), T.SatisfiesWeaveRules ∧ T.FormsWeavePattern :=
  ⟨(periodic n hn).toTiling, (periodic n hn).toTiling_satisfiesWeaveRules,
    (periodic n hn).toTiling_formsWeavePattern⟩

end Schematic

end StickPolyhex
