import Tiling.Proofs.GapAssignment

/-!
# The schematic built from abstract gap data

Given `A : GapAssignment G` — a state for every row and a pair of values for every gap, subject
to the conditions of Section 2.5 of the paper — this file builds the schematic `A.toSchematic`
whose gaps are placed exactly as prescribed by `A` (see `Tiling/Proofs/GapAssignment.lean` for
the layout).

The columns of the row `r` are cut into consecutive pieces by the numbers `gapStart r k` and
`gapEnd r k`: the columns `gapStart r k, …, gapEnd r k - 1` form the `k`-th gap of the row (its
first `lenLz r k` columns being its left part), and the columns `gapEnd r k, …, gapEnd r k + N`
form the block that follows it, where `N = G.blockLen`.  Since consecutive gaps are at distance
`lenz + N + 1`, every column lies in exactly one such piece; `A.idx r x` is the index of the
piece containing the column `x`, and `A.slotAt r x` reads off its slot.

The two axioms of a schematic are then verified: `slot_step` by inspecting the six possible
positions of a column inside its piece, and `slot_overlap` by the arithmetic of
`GapAssignment.two_le_offz` and `GapAssignment.offz_add_lenz_le`.
-/

namespace StickPolyhex

namespace GapAssignment

variable {G : GapSpec} (A : GapAssignment G)

/-! ### Locating a column -/

lemma exists_index (r x : ℤ) : ∃ k, A.gapStart r k ≤ x ∧ x < A.gapStart r (k + 1) := by
  have hmono := A.gapStart_strictMono r
  have up : ∀ d : ℕ, ∃ k, A.gapStart r k ≤ A.gapStart r 0 + d ∧
      A.gapStart r 0 + d < A.gapStart r (k + 1) := by
    intro d
    induction d with
    | zero => exact ⟨0, by simp, by simpa using A.gapStart_lt_succ r 0⟩
    | succ e ih =>
      obtain ⟨k, h1, h2⟩ := ih
      by_cases hc : A.gapStart r 0 + ((e : ℤ) + 1) < A.gapStart r (k + 1)
      · exact ⟨k, by push_cast; omega, by push_cast; omega⟩
      · refine ⟨k + 1, by push_cast; omega, ?_⟩
        have := A.gapStart_lt_succ r (k + 1)
        push_cast
        omega
  have down : ∀ d : ℕ, ∃ k, A.gapStart r k ≤ A.gapStart r 0 - d ∧
      A.gapStart r 0 - d < A.gapStart r (k + 1) := by
    intro d
    induction d with
    | zero => exact ⟨0, by simp, by simpa using A.gapStart_lt_succ r 0⟩
    | succ e ih =>
      obtain ⟨k, h1, h2⟩ := ih
      by_cases hc : A.gapStart r k ≤ A.gapStart r 0 - ((e : ℤ) + 1)
      · exact ⟨k, by push_cast; omega, by push_cast; omega⟩
      · refine ⟨k - 1, ?_, ?_⟩
        · have := hmono (show k - 1 < k by omega)
          push_cast
          omega
        · rw [show k - 1 + 1 = k by ring]
          push_cast
          omega
  rcases le_or_gt (A.gapStart r 0) x with hx | hx
  · obtain ⟨k, h1, h2⟩ := up (x - A.gapStart r 0).toNat
    exact ⟨k, by omega, by omega⟩
  · obtain ⟨k, h1, h2⟩ := down (A.gapStart r 0 - x).toNat
    exact ⟨k, by omega, by omega⟩

/-- The index of the gap of the row `r` whose gap-and-block piece contains the column `x`. -/
noncomputable def idx (r x : ℤ) : ℤ := (A.exists_index r x).choose

lemma idx_le (r x : ℤ) : A.gapStart r (A.idx r x) ≤ x := (A.exists_index r x).choose_spec.1

lemma lt_idx_succ (r x : ℤ) : x < A.gapStart r (A.idx r x + 1) :=
  (A.exists_index r x).choose_spec.2

lemma idx_eq {r x k : ℤ} (h1 : A.gapStart r k ≤ x) (h2 : x < A.gapStart r (k + 1)) :
    A.idx r x = k := by
  have hmono := (A.gapStart_strictMono r).monotone
  have hl := A.idx_le r x
  have hr := A.lt_idx_succ r x
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (lt_of_lt_of_le hr (hmono (show A.idx r x + 1 ≤ k by omega))) (by omega)
  · exact absurd (lt_of_lt_of_le h2 (hmono (show k + 1 ≤ A.idx r x by omega))) (by omega)

/-! ### The slots -/

/-- The slot of the column `x` of the row `r` of the schematic prescribed by `A`. -/
noncomputable def slotAt (r x : ℤ) : Slot :=
  if x - A.gapStart r (A.idx r x) < A.lenLz r (A.idx r x) then .gapL
  else if x < A.gapEnd r (A.idx r x) then .gapR
  else .block (x - A.gapEnd r (A.idx r x)).toNat

lemma slotAt_gapL {r x k : ℤ} (h1 : A.gapStart r k ≤ x) (h2 : x < A.gapStart r k + A.lenLz r k) :
    A.slotAt r x = .gapL := by
  have hk : A.idx r x = k := by
    refine A.idx_eq h1 ?_
    have h3 := A.gapStart_succ r k
    have h4 := A.one_le_lenRz r k
    have h5 := G.blockLenZ
    have h6 := G.two_v_le_lbZ
    have h7 : (0 : ℤ) ≤ (G.s : ℤ) * G.lbZ := by
      apply mul_nonneg <;> [exact_mod_cast Nat.zero_le _; omega]
    have := G.hv
    simp only [gapEnd, lenz] at h3
    omega
  simp only [slotAt, hk, if_pos (show x - A.gapStart r k < A.lenLz r k by omega)]

lemma slotAt_gapR {r x k : ℤ} (h1 : A.gapStart r k + A.lenLz r k ≤ x) (h2 : x < A.gapEnd r k) :
    A.slotAt r x = .gapR := by
  have hk : A.idx r x = k := by
    refine A.idx_eq (by have := A.one_le_lenLz r k; omega) ?_
    exact lt_trans h2 (A.gapEnd_lt_gapStart_succ r k)
  simp only [slotAt, hk, if_neg (show ¬ (x - A.gapStart r k < A.lenLz r k) by omega),
    if_pos h2]

lemma slotAt_block {r x k : ℤ} (h1 : A.gapEnd r k ≤ x) (h2 : x ≤ A.gapEnd r k + (G.blockLen : ℤ)) :
    A.slotAt r x = .block (x - A.gapEnd r k).toNat := by
  have hg := A.gapStart_lt_gapEnd r k
  have hk : A.idx r x = k := by
    refine A.idx_eq (by omega) ?_
    rw [A.gapStart_succ r k]
    omega
  have hlen : A.gapStart r k + A.lenLz r k ≤ x := by
    have := A.one_le_lenRz r k
    simp only [gapEnd, lenz] at h1
    omega
  simp only [slotAt, hk, if_neg (show ¬ (x - A.gapStart r k < A.lenLz r k) by omega),
    if_neg (show ¬ (x < A.gapEnd r k) by omega)]

/-- Every column lies either in a gap or in a block. -/
lemma slotAt_trichotomy (r x : ℤ) :
    (A.gapStart r (A.idx r x) ≤ x ∧ x < A.gapStart r (A.idx r x) + A.lenLz r (A.idx r x)) ∨
      (A.gapStart r (A.idx r x) + A.lenLz r (A.idx r x) ≤ x ∧ x < A.gapEnd r (A.idx r x)) ∨
      (A.gapEnd r (A.idx r x) ≤ x ∧ x ≤ A.gapEnd r (A.idx r x) + (G.blockLen : ℤ)) := by
  have h1 := A.idx_le r x
  have h2 := A.lt_idx_succ r x
  rw [A.gapStart_succ r (A.idx r x)] at h2
  omega

lemma gapEnd_eq (r k : ℤ) : A.gapEnd r k = A.gapStart r k + A.lenLz r k + A.lenRz r k := by
  simp only [gapEnd, lenz]; ring

lemma exists_of_isGap {r x : ℤ} (h : (A.slotAt r x).IsGap) :
    ∃ k, A.gapStart r k ≤ x ∧ x < A.gapEnd r k := by
  have hE := A.gapEnd_eq r (A.idx r x)
  have hL := A.one_le_lenLz r (A.idx r x)
  have hR := A.one_le_lenRz r (A.idx r x)
  rcases A.slotAt_trichotomy r x with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨A.idx r x, ha, by omega⟩
  · exact ⟨A.idx r x, by omega, hb⟩
  · rw [A.slotAt_block ha hb] at h
    exact h.elim

lemma exists_of_gapL {r x : ℤ} (h : A.slotAt r x = .gapL) :
    ∃ k, A.gapStart r k ≤ x ∧ x < A.gapStart r k + A.lenLz r k := by
  rcases A.slotAt_trichotomy r x with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨A.idx r x, ha, hb⟩
  · rw [A.slotAt_gapR ha hb] at h; exact Slot.noConfusion h
  · rw [A.slotAt_block ha hb] at h; exact Slot.noConfusion h

/-! ### The schematic -/

lemma step_aux (r x : ℤ) : Slot.Step G.blockLen (A.slotAt r x) (A.slotAt r (x + 1)) := by
  have htri := A.slotAt_trichotomy r x
  set k := A.idx r x with hkdef
  have hL := A.one_le_lenLz r k
  have hR := A.one_le_lenRz r k
  have hE : A.gapEnd r k = A.gapStart r k + A.lenLz r k + A.lenRz r k := by
    simp only [gapEnd, lenz]; ring
  have hS := A.gapStart_succ r k
  rcases htri with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [A.slotAt_gapL ha hb]
    rcases lt_or_ge (x + 1) (A.gapStart r k + A.lenLz r k) with hc | hc
    · rw [A.slotAt_gapL (by omega) hc]; trivial
    · rw [A.slotAt_gapR (by omega) (by omega)]; trivial
  · rw [A.slotAt_gapR ha hb]
    rcases lt_or_ge (x + 1) (A.gapEnd r k) with hc | hc
    · rw [A.slotAt_gapR (by omega) hc]; trivial
    · rw [A.slotAt_block (by omega) (by omega)]
      simp only [Slot.Step]
      omega
  · rw [A.slotAt_block ha hb]
    rcases lt_or_ge x (A.gapEnd r k + (G.blockLen : ℤ)) with hc | hc
    · rw [A.slotAt_block (k := k) (by omega) (by omega)]
      simp only [Slot.Step]
      omega
    · have hx : x = A.gapEnd r k + (G.blockLen : ℤ) := by omega
      rw [A.slotAt_gapL (k := k + 1) (by omega) (by have := A.one_le_lenLz r (k + 1); omega)]
      simp only [Slot.Step]
      omega

lemma overlap_aux (r x : ℤ) (h : (A.slotAt (r + 1) x).IsGap) :
    ∃ j, 2 ≤ j ∧ j + 1 ≤ G.blockLen ∧ A.slotAt r x = .block j := by
  obtain ⟨k, h1, h2⟩ := A.exists_of_isGap h
  have hshift := A.gapStart_shift r k
  have hoff := A.two_le_offz (r + 1) k
  have hsum := A.offz_add_lenz_le (r + 1) k
  have hE : A.gapEnd (r + 1) k = A.gapStart (r + 1) k + A.lenz (r + 1) k := rfl
  have hE2 := A.gapEnd_eq r k
  refine ⟨(x - A.gapEnd r k).toNat, by omega, by omega, ?_⟩
  exact A.slotAt_block (by omega) (by omega)

/-- The schematic prescribed by the gap data `A`. -/
noncomputable def toSchematic : Schematic G.blockLen where
  slot := A.slotAt
  slot_step := A.step_aux
  slot_overlap := A.overlap_aux

@[simp] lemma toSchematic_slot (r x : ℤ) : A.toSchematic.slot r x = A.slotAt r x := rfl

end GapAssignment

end StickPolyhex
