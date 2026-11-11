import Tiling.Proofs.GapSchematic
import Tiling.Proofs.SchematicWeave

/-!
# Every family of admissible states and values comes from a schematic

This file completes the construction begun in `Tiling/Proofs/GapAssignment.lean` and
`Tiling/Proofs/GapSchematic.lean`: the schematic `A.toSchematic` built from the abstract gap
data `A : GapAssignment G` has exactly the prescribed gaps, and it satisfies the gap conditions
of Section 2.5 of the paper for the prescribed states.

## Main results

* `GapAssignment.gapData`: the `k`-th gap of the row `r` of `A.toSchematic` occupies the columns
  `gapStart r k, …`, its left part has `lnat r k` columns and its right part `mnat r k`, and it
  starts above the column `jnat r k` of the block below it;
* `GapAssignment.lval_eq`, `GapAssignment.rval_eq`: the two values of that gap are the prescribed
  `xv r k` and `yv r k`;
* `GapAssignment.gapAt_eq`: conversely, every gap of `A.toSchematic` is one of these;
* `GapAssignment.toSchematic_gapConditions`: `A.toSchematic` satisfies the gap conditions with
  the state function `A.st`;
* `Schematic.exists_of_gapAssignment`: consequently, admissible states and values are always
  realised by a schematic, which moreover respects the marks `G.marking`;
* `GapSpec.exists_tiling_of_gapAssignment`: and hence by a weave-pattern tiling of the plane by
  the marked stick of length `G.blockLen + 1`.

Together with `Schematic.respectsMarking_iff_gapConditions` this shows that the gap conditions
are exactly the combinatorial shadow of the tilings: they can be read off a tiling, and every
family of states and values satisfying them comes from one.
-/

namespace StickPolyhex

namespace GapAssignment

variable {G : GapSpec} (A : GapAssignment G)

/-! ### The gaps of the schematic, as natural numbers -/

/-- The number of columns of the left part of the `k`-th gap of the row `r`. -/
noncomputable def lnat (r k : ℤ) : ℕ := (A.lenLz r k).toNat

/-- The number of columns of the right part of the `k`-th gap of the row `r`. -/
noncomputable def mnat (r k : ℤ) : ℕ := (A.lenRz r k).toNat

/-- The column of the block below above which the `k`-th gap of the row `r` starts. -/
noncomputable def jnat (r k : ℤ) : ℕ := (A.offz r k).toNat

@[simp] lemma lnat_cast (r k : ℤ) : ((A.lnat r k : ℕ) : ℤ) = A.lenLz r k :=
  Int.toNat_of_nonneg (by have := A.one_le_lenLz r k; omega)

@[simp] lemma mnat_cast (r k : ℤ) : ((A.mnat r k : ℕ) : ℤ) = A.lenRz r k :=
  Int.toNat_of_nonneg (by have := A.one_le_lenRz r k; omega)

@[simp] lemma jnat_cast (r k : ℤ) : ((A.jnat r k : ℕ) : ℤ) = A.offz r k :=
  Int.toNat_of_nonneg (by have := A.two_le_offz r k; omega)

/-! ### The gaps of the schematic -/

lemma gapAt (r k : ℤ) :
    A.toSchematic.GapAt r (A.gapStart r k) (A.lnat r k) (A.mnat r k) := by
  have hE := A.gapEnd_eq r k
  have hL := A.one_le_lenLz r k
  have hR := A.one_le_lenRz r k
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hprev : A.gapStart r k = A.gapEnd r (k - 1) + (G.blockLen : ℤ) + 1 := by
      have := A.gapStart_succ r (k - 1)
      rwa [show k - 1 + 1 = k by ring] at this
    have := A.slotAt_block (r := r) (k := k - 1) (x := A.gapStart r k - 1) (by omega) (by omega)
    rw [toSchematic_slot, this]
    congr 1
    omega
  · intro c hc
    rw [toSchematic_slot]
    refine A.slotAt_gapL (k := k) (by omega) ?_
    have : (c : ℤ) < A.lenLz r k := by
      have := A.lnat_cast r k
      omega
    omega
  · intro c hc
    rw [toSchematic_slot]
    refine A.slotAt_gapR (k := k) (by simp) ?_
    have : (c : ℤ) < A.lenRz r k := by
      have := A.mnat_cast r k
      omega
    simp only [lnat_cast]
    omega
  · rw [toSchematic_slot]
    have hx : A.gapStart r k + (A.lnat r k : ℤ) + (A.mnat r k : ℤ) = A.gapEnd r k := by
      simp only [lnat_cast, mnat_cast]
      omega
    rw [hx, A.slotAt_block (k := k) (le_refl _) (by
      have := G.blockLenZ
      have := G.two_v_le_lbZ
      have := G.hv
      have h : (0 : ℤ) ≤ (G.s : ℤ) * G.lbZ := by
        apply mul_nonneg <;> [exact_mod_cast Nat.zero_le _; omega]
      omega)]
    congr 1
    omega

lemma offz_le_blockLen (r k : ℤ) : A.offz r k + 2 ≤ (G.blockLen : ℤ) := by
  have := A.offz_add_lenz_le r k
  have := A.two_le_lenz r k
  omega

lemma slot_below_gapStart (r k : ℤ) :
    A.toSchematic.slot (r - 1) (A.gapStart r k) = .block (A.jnat r k) := by
  have hshift := A.gapStart_shift (r - 1) k
  rw [show r - 1 + 1 = r by ring] at hshift
  have hoff := A.two_le_offz r k
  have hle := A.offz_le_blockLen r k
  rw [toSchematic_slot, A.slotAt_block (k := k) (by omega) (by omega)]
  congr 1
  simp only [jnat]
  omega

/-- The `k`-th gap of the row `r` of the schematic built from `A`. -/
lemma gapData (r k : ℤ) :
    A.toSchematic.GapData r (A.gapStart r k) (A.lnat r k) (A.mnat r k) (A.jnat r k) :=
  ⟨A.gapAt r k, A.slot_below_gapStart r k⟩

/-- The left value of the `k`-th gap of the row `r` is the prescribed one. -/
lemma lval_eq (r k : ℤ) : G.lval (A.st (r - 1)) (A.lnat r k) = A.xv r k := by
  simp only [GapSpec.lval, lnat_cast, lenLz]
  ring

/-- The right value of the `k`-th gap of the row `r` is the prescribed one. -/
lemma rval_eq (r k : ℤ) : G.rval (A.st (r - 1)) (A.mnat r k) = A.yv r k := by
  simp only [GapSpec.rval, mnat_cast, lenRz]
  ring

/-- The block following a gap, in terms of the natural-number lengths. -/
lemma gapEnd_nat (r k : ℤ) :
    A.gapEnd r k = A.gapStart r k + (A.lnat r k : ℤ) + (A.mnat r k : ℤ) := by
  simp only [lnat_cast, mnat_cast]
  exact A.gapEnd_eq r k

/-! ### Every gap of the schematic is one of these -/

lemma gapAt_eq {r u : ℤ} {l m : ℕ} (h : A.toSchematic.GapAt r u l m) :
    ∃ k, u = A.gapStart r k ∧ l = A.lnat r k ∧ m = A.mnat r k := by
  have hu : A.slotAt r u = .gapL := by
    have := h.slot_gapL (k := 0) h.l_pos
    simpa using this
  obtain ⟨k, h1, h2⟩ := A.exists_of_gapL hu
  have hk : u = A.gapStart r k := by
    by_contra hne
    have hprev : A.slotAt r (u - 1) = .gapL := A.slotAt_gapL (k := k) (by omega) (by omega)
    have := h.blockLeft
    rw [toSchematic_slot, hprev] at this
    exact Slot.noConfusion this
  subst hk
  obtain ⟨hl, hm⟩ := h.unique (A.gapAt r k)
  exact ⟨k, rfl, hl, hm⟩

lemma gapData_eq {r u : ℤ} {l m j : ℕ} (h : A.toSchematic.GapData r u l m j) :
    ∃ k, u = A.gapStart r k ∧ l = A.lnat r k ∧ m = A.mnat r k ∧ j = A.jnat r k := by
  obtain ⟨k, hu, hl, hm⟩ := A.gapAt_eq h.toGapAt
  refine ⟨k, hu, hl, hm, ?_⟩
  have h1 := h.slot_below
  rw [hu, A.slot_below_gapStart r k] at h1
  injection h1 with e
  exact e.symm

/-! ### Identifying the neighbouring gaps -/

/-- The gap of the row `r - 1` whose block carries the `k`-th gap of the row `r` on its left. -/
lemma gapEnd_left {r : ℤ} (k k' : ℤ)
    (heY : A.gapStart (r - 1) k' + (A.lnat (r - 1) k' : ℤ) + (A.mnat (r - 1) k' : ℤ)
      = A.gapStart r k - (A.jnat r k : ℤ)) : k' = k := by
  refine (A.gapEnd_strictMono (r - 1)).injective ?_
  have hE := A.gapEnd_nat (r - 1) k'
  have hshift := A.gapStart_shift (r - 1) k
  rw [show r - 1 + 1 = r by ring] at hshift
  have hj := A.jnat_cast r k
  omega

/-- The gap of the row `r - 1` lying to the right of the block that carries the `k`-th gap of the
row `r`. -/
lemma gapStart_right {r : ℤ} (k k' : ℤ)
    (hZu : A.gapStart r k - (A.jnat r k : ℤ) + (G.blockLen : ℤ) + 1 = A.gapStart (r - 1) k') :
    k' = k + 1 := by
  refine (A.gapStart_strictMono (r - 1)).injective ?_
  rw [A.gapStart_succ (r - 1) k]
  have hshift := A.gapStart_shift (r - 1) k
  rw [show r - 1 + 1 = r by ring] at hshift
  have hj := A.jnat_cast r k
  omega

/-! ### The gap conditions -/

lemma toSchematic_gapConditions : A.toSchematic.GapConditions G A.st where
  state_mem r := A.state_mem r
  state_cycle r := A.state_cycle r
  left_value := by
    rintro r u l m j hg
    obtain ⟨k, hu, hl, hm, hj⟩ := A.gapData_eq hg
    subst hl
    rw [A.lval_eq r k]
    exact A.x_mem r k
  right_value := by
    rintro r u l m j hg
    obtain ⟨k, hu, hl, hm, hj⟩ := A.gapData_eq hg
    subst hm
    rw [A.rval_eq r k]
    exact A.y_mem r k
  align_left := by
    rintro r u l m j hg uY lY mY jY hY heY
    obtain ⟨k, hu, hl, hm, hj⟩ := A.gapData_eq hg
    obtain ⟨k', huY, hlY, hmY, hjY⟩ := A.gapData_eq hY
    subst hu hl hm hj huY hlY hmY hjY
    have hkk : k' = k := A.gapEnd_left k k' heY
    subst hkk
    have hrv := A.rval_eq (r - 1) k'
    rw [show r - 1 - 1 = r - 2 by ring] at hrv
    rw [hrv]
    simp only [jnat_cast, offz]
    ring
  align_right := by
    rintro r u l m j hg lZ mZ jZ hZ
    obtain ⟨k, hu, hl, hm, hj⟩ := A.gapData_eq hg
    obtain ⟨k', hZu, hlZ, hmZ, hjZ⟩ := A.gapData_eq hZ
    subst hu hl hm hj hlZ hmZ hjZ
    have hkk : k' = k + 1 := A.gapStart_right k k' hZu
    subst hkk
    have hlv := A.lval_eq (r - 1) (k + 1)
    rw [show r - 1 - 1 = r - 2 by ring] at hlv
    rw [hlv]
    have hsum := A.value_sum r k
    have hlb := G.lbZ_eq
    simp only [jnat_cast, lnat_cast, mnat_cast, offz, lenLz, lenRz]
    linarith [hsum, hlb]
  interval := by
    rintro r u l m j hg uY lY mY jY hY heY
    obtain ⟨k, hu, hl, hm, hj⟩ := A.gapData_eq hg
    obtain ⟨k', huY, hlY, hmY, hjY⟩ := A.gapData_eq hY
    subst hu hl hm hj huY hlY hmY hjY
    have hkk : k' = k := A.gapEnd_left k k' heY
    subst hkk
    have hrv := A.rval_eq (r - 1) k'
    rw [show r - 1 - 1 = r - 2 by ring] at hrv
    rw [hrv, A.lval_eq r k']
    exact A.interval r k'

lemma toSchematic_satisfiesGapConditions : A.toSchematic.SatisfiesGapConditions G :=
  ⟨A.st, A.toSchematic_gapConditions⟩

/-- The schematic built from `A` respects the marks that the construction of Section 2.5 places
on the block. -/
lemma toSchematic_respectsMarking : A.toSchematic.RespectsMarking G.marking :=
  Schematic.respectsMarking_of_gapConditions A.toSchematic_satisfiesGapConditions

end GapAssignment

namespace Schematic

/-- **A block schematic can be reconstructed from the states and the values of its gaps.**
Given a state for every row and two values for every gap satisfying the gap conditions of
Section 2.5 of the paper, there is a schematic `S` realising them: its rows have gaps starting
at the columns `u r k`, listed from left to right and exhausting all the gaps of the row, the
`k`-th gap of the row `r` having left value `xv r k` and right value `yv r k`.  The schematic
satisfies the gap conditions with the given states, and
therefore respects the marks that Section 2.5 places on the block.

The horizontal position of a whole schematic is of course not determined by the data; but the
*relative* offset of two adjacent rows is, namely by the formula
`GapAssignment.gapStart_shift`. -/
theorem exists_of_gapAssignment {G : GapSpec} (A : GapAssignment G) :
    ∃ (S : Schematic G.blockLen) (u : ℤ → ℤ → ℤ),
      S.GapConditions G A.st ∧ S.RespectsMarking G.marking ∧
      (∀ r, StrictMono (u r)) ∧
      (∀ r k : ℤ, ∃ l m j, S.GapData r (u r k) l m j ∧
        G.lval (A.st (r - 1)) l = A.xv r k ∧ G.rval (A.st (r - 1)) m = A.yv r k) ∧
      (∀ (r u' : ℤ) (l m : ℕ), S.GapAt r u' l m → ∃ k, u' = u r k) :=
  ⟨A.toSchematic, A.gapStart, A.toSchematic_gapConditions, A.toSchematic_respectsMarking,
    A.gapStart_strictMono,
    fun r k => ⟨A.lnat r k, A.mnat r k, A.jnat r k, A.gapData r k, A.lval_eq r k, A.rval_eq r k⟩,
    fun _ _ _ _ h => by obtain ⟨k, hk, -, -⟩ := A.gapAt_eq h; exact ⟨k, hk⟩⟩

end Schematic

namespace GapSpec

/-- Admissible states and values give rise to an actual tiling of the plane by the stick of
length `G.blockLen + 1` decorated by the marks of Section 2.5. -/
theorem exists_tiling_of_gapAssignment {G : GapSpec} (A : GapAssignment G) :
    ∃ T : StickTiling (G.blockLen + 1),
      T.SatisfiesRules (markedRules G.blockLen G.marking) ∧ T.FormsWeavePattern :=
  ⟨A.toSchematic.toTiling,
    (Schematic.toTiling_satisfiesRules_iff_gapConditions).2 A.toSchematic_satisfiesGapConditions,
    A.toSchematic.toTiling_formsWeavePattern⟩

end GapSpec

end StickPolyhex
