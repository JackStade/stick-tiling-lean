import Tiling.Proofs.SchematicStacks

/-!
# The stacks of a schematic tiling as explicit finite sets

Using the characterisation `Schematic.sameStack_iff` of the relation `StickTiling.SameStack` for
the tiling of a schematic, this file lists the sticks of a stack and computes the height of a
stack:

* `Schematic.stackHeight_block`: a block is a stack of exactly `n + 1` horizontal sticks;
* `Schematic.stackHeight_gap`: a gap of `t` columns is a stack of exactly `t` left-slanting
  sticks.
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-! ### Horizontal stacks -/

/-- The representative cells of the `n + 1` sticks of a block: the cells of the leftmost column
of the block. -/
lemma slotAt_blockRep {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) {i : ℤ} (h0 : 0 ≤ i)
    (hi : i ≤ n) :
    S.slotAt (shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c + i)) = .block 0 ∧
      S.bandOf (shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c + i)) = S.bandOf c := by
  have hb : bandRow n (((n : ℤ) + 1) * S.bandOf c + i) = S.bandOf c := bandRow_eq n _ _ h0 hi
  refine ⟨?_, by rw [bandOf_shearCell, hb]⟩
  rw [slotAt_shearCell, hb]
  exact S.slot_block_start h

/-- The stack of a cell of a block consists of the `n + 1` horizontal sticks filling the
block. -/
lemma stack_eq_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.toTiling.Stack c = ↑((Finset.range (n + 1)).image
      (fun i : ℕ => S.toTiling.stickOf
        (shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c + i)))) := by
  ext s
  simp only [StickTiling.Stack, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [S.sameStack_iff] at hx
    rcases hx with ⟨jc, jx, hjc, hjx, hband, hcol⟩ | ⟨hg, -, -, -⟩
    · rw [h] at hjc
      injection hjc with e
      subst e
      have h0 := S.subOf_nonneg x
      have hn := S.subOf_le x
      refine ⟨(S.subOf x).toNat, by omega, ?_⟩
      have hi : (((S.subOf x).toNat : ℕ) : ℤ) = S.subOf x := by omega
      have hrow : ((n : ℤ) + 1) * S.bandOf c + (((S.subOf x).toNat : ℕ) : ℤ) = shearRow x := by
        rw [hi, hband]
        have := bandRow_mul_add n (shearRow x)
        simp only [bandOf, subOf] at *
        omega
      refine S.toTiling.stickOf_eq_of_mem ?_
      rw [S.mem_stickOf_block_iff hjx, shearRow_shearCell, shearCol_shearCell, hrow, hcol]
      exact ⟨rfl, le_rfl, by omega⟩
    · rw [h] at hg; exact hg.elim
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hz, hbz⟩ := S.slotAt_blockRep h (i := (i : ℤ)) (by positivity) (by omega)
    exact ⟨_, (S.sameStack_iff _ _).2 (Or.inl ⟨j, 0, h, hz, hbz.symm, by simp⟩), rfl⟩

/-- A block is a stack of exactly `n + 1` horizontal sticks. -/
theorem stackHeight_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.toTiling.stackHeight c = n + 1 := by
  rw [StickTiling.stackHeight, S.stack_eq_block h, Set.ncard_coe_finset,
    Finset.card_image_of_injOn, Finset.card_range]
  intro i hi i' hi' hii
  simp only [Finset.mem_coe, Finset.mem_range] at hi hi'
  obtain ⟨hz, -⟩ := S.slotAt_blockRep h (i := (i' : ℤ)) (by positivity) (by omega)
  have hii' : S.toTiling.stickOf (shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c + i))
      = S.toTiling.stickOf (shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c + i')) := hii
  have hmem : shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c + i)
      ∈ S.toTiling.stickOf (shearCell (shearCol c - j) (((n : ℤ) + 1) * S.bandOf c + i')) := by
    rw [← hii']
    exact S.toTiling.self_mem_stickOf _
  rw [S.mem_stickOf_block_iff hz, shearRow_shearCell, shearRow_shearCell] at hmem
  have := hmem.1
  omega

/-! ### Vertical stacks -/

/-- The stack of a cell of a gap consists of the left-slanting sticks filling the columns of the
gap. -/
lemma stack_eq_gap {v : Hex} (hv : (S.slotAt v).IsGap) {g2 : ℤ} (hle : shearCol v ≤ g2)
    (hall : ∀ y : ℤ, shearCol v ≤ y → y ≤ g2 → (S.slot (S.bandOf v) y).IsGap)
    (hl : ¬ (S.slot (S.bandOf v) (shearCol v - 1)).IsGap)
    (hr : ¬ (S.slot (S.bandOf v) (g2 + 1)).IsGap) :
    S.toTiling.Stack v = ↑((Finset.Icc (shearCol v) g2).image
      (fun y : ℤ => S.toTiling.stickOf (shearCell y (((n : ℤ) + 1) * S.bandOf v)))) := by
  have hbrep : ∀ y : ℤ, S.bandOf (shearCell y (((n : ℤ) + 1) * S.bandOf v)) = S.bandOf v := by
    intro y
    rw [bandOf_shearCell,
      show ((n : ℤ) + 1) * S.bandOf v = ((n : ℤ) + 1) * S.bandOf v + 0 from by ring,
      bandRow_eq n _ _ le_rfl (by positivity)]
  have hsrep : ∀ y : ℤ, S.slotAt (shearCell y (((n : ℤ) + 1) * S.bandOf v))
      = S.slot (S.bandOf v) y := by
    intro y
    rw [slotAt_eq, shearCol_shearCell, hbrep]
  ext s
  simp only [StickTiling.Stack, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, Finset.mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [S.sameStack_iff] at hx
    rcases hx with ⟨jv, -, hjv, -, -, -⟩ | ⟨-, hgx, hband, hy⟩
    · rw [hjv] at hv; exact hv.elim
    · have hb1 : shearCol v ≤ shearCol x := by
        by_contra hc
        exact hl (hy _ (Or.inr ⟨by omega, by omega⟩))
      have hb2 : shearCol x ≤ g2 := by
        by_contra hc
        exact hr (hy _ (Or.inl ⟨by omega, by omega⟩))
      refine ⟨shearCol x, ⟨hb1, hb2⟩, ?_⟩
      refine S.toTiling.stickOf_eq_of_mem ?_
      rw [S.mem_stickOf_gap_iff hgx, shearCol_shearCell, hbrep, hband]
      exact ⟨rfl, rfl⟩
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨_, (S.sameStack_iff _ _).2 (Or.inr ⟨hv, ?_, (hbrep y).symm, ?_⟩), rfl⟩
    · rw [hsrep]; exact hall y hy1 hy2
    · intro z hz
      rw [shearCol_shearCell] at hz
      exact hall z (by omega) (by omega)

/-- A gap of `t` columns is a stack of exactly `t` left-slanting sticks. -/
theorem stackHeight_gap {v : Hex} (hv : (S.slotAt v).IsGap) {g2 : ℤ} (hle : shearCol v ≤ g2)
    (hall : ∀ y : ℤ, shearCol v ≤ y → y ≤ g2 → (S.slot (S.bandOf v) y).IsGap)
    (hl : ¬ (S.slot (S.bandOf v) (shearCol v - 1)).IsGap)
    (hr : ¬ (S.slot (S.bandOf v) (g2 + 1)).IsGap) :
    S.toTiling.stackHeight v = (g2 + 1 - shearCol v).toNat := by
  have hbrep : ∀ y : ℤ, S.bandOf (shearCell y (((n : ℤ) + 1) * S.bandOf v)) = S.bandOf v := by
    intro y
    rw [bandOf_shearCell,
      show ((n : ℤ) + 1) * S.bandOf v = ((n : ℤ) + 1) * S.bandOf v + 0 from by ring,
      bandRow_eq n _ _ le_rfl (by positivity)]
  have hsrep : ∀ y : ℤ, S.slotAt (shearCell y (((n : ℤ) + 1) * S.bandOf v))
      = S.slot (S.bandOf v) y := by
    intro y
    rw [slotAt_eq, shearCol_shearCell, hbrep]
  rw [StickTiling.stackHeight, S.stack_eq_gap hv hle hall hl hr, Set.ncard_coe_finset,
    Finset.card_image_of_injOn, Int.card_Icc]
  intro y hy y' hy' hyy
  simp only [Finset.mem_coe, Finset.mem_Icc] at hy hy'
  have hgap' : (S.slotAt (shearCell y' (((n : ℤ) + 1) * S.bandOf v))).IsGap := by
    rw [hsrep]; exact hall y' hy'.1 hy'.2
  have hyy' : S.toTiling.stickOf (shearCell y (((n : ℤ) + 1) * S.bandOf v))
      = S.toTiling.stickOf (shearCell y' (((n : ℤ) + 1) * S.bandOf v)) := hyy
  have hmem : shearCell y (((n : ℤ) + 1) * S.bandOf v)
      ∈ S.toTiling.stickOf (shearCell y' (((n : ℤ) + 1) * S.bandOf v)) := by
    rw [← hyy']
    exact S.toTiling.self_mem_stickOf _
  rw [S.mem_stickOf_gap_iff hgap', shearCol_shearCell, shearCol_shearCell] at hmem
  exact hmem.1

end Schematic

end StickPolyhex
