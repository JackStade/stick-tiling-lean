import Tiling.Proofs.SchematicTiling

/-!
# The sticks of the tiling described by a schematic

This file identifies the sticks of `Schematic.toTiling`: the stick through a cell of a block is
the set of cells of its row lying in that block (`Schematic.mem_stickOf_block_iff`), and the
stick through a cell of a gap is the set of cells of its column lying in its band
(`Schematic.mem_stickOf_gap_iff`).
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} (S : Schematic n)

/-! ### Walks in sheared coordinates -/

lemma walk_W (c : Hex) (k : ℤ) : walk c HexDir.W k = shearCell (shearCol c - k) (shearRow c) := by
  simp [walk, shearCell, shearCol, shearRow, HexDir.vec, HexDir.W, Prod.ext_iff]
  ring

lemma walk_NW (c : Hex) (k : ℤ) :
    walk c HexDir.NW k = shearCell (shearCol c) (shearRow c + k) := by
  simp [walk, shearCell, shearCol, shearRow, HexDir.vec, HexDir.NW, Prod.ext_iff]
  ring

lemma walk_SE (c : Hex) (k : ℤ) :
    walk c HexDir.SE k = shearCell (shearCol c) (shearRow c - k) := by
  simp [walk, shearCell, shearCol, shearRow, HexDir.vec, HexDir.SE, Prod.ext_iff]
  omega

/-! ### Slots of constructed cells -/

@[simp] lemma slotAt_shearCell (x q : ℤ) : S.slotAt (shearCell x q) = S.slot (bandRow n q) x := by
  rw [slotAt, bandOf, shearCol_shearCell, shearRow_shearCell]

@[simp] lemma bandOf_shearCell (x q : ℤ) : S.bandOf (shearCell x q) = bandRow n q := rfl

lemma slotAt_eq (c : Hex) : S.slotAt c = S.slot (S.bandOf c) (shearCol c) := rfl

lemma slotAt_block_le {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) : j ≤ n :=
  S.block_le (r := S.bandOf c) (x := shearCol c) h

/-- The block column at distance `k` from the left end of the block of a block cell. -/
lemma slotAt_of_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) {k : ℕ} (hk : k ≤ n) :
    S.slot (S.bandOf c) (shearCol c - j + k) = .block k :=
  S.slot_block_of_block (r := S.bandOf c) (x := shearCol c) h hk

/-- The column just left of the block of a block cell is a gap column. -/
lemma slot_gapR_of_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.slot (S.bandOf c) (shearCol c - j - 1) = .gapR :=
  S.gapR_of_block (r := S.bandOf c) (x := shearCol c) h

/-- The column just right of the block of a block cell is a gap column. -/
lemma slot_gapL_of_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.slot (S.bandOf c) (shearCol c - j + n + 1) = .gapL :=
  S.gapL_of_block_n (r := S.bandOf c) (x := shearCol c) h

/-! ### Heads of sticks -/

lemma head_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.toTiling.head c = shearCell (shearCol c - j + n) (shearRow c) := by
  have hj : j ≤ n := S.slotAt_block_le h
  rw [StickTiling.head, toTiling_dir, toTiling_idx, S.dirAt_block h, S.idxAt_block h, walk_W]
  have hcast : ((n + 1 - j : ℕ) : ℤ) = (n : ℤ) + 1 - j := by omega
  rw [hcast]
  congr 1
  ring

lemma head_gapL {c : Hex} (h : S.slotAt c = .gapL) :
    S.toTiling.head c = shearCell (shearCol c) (((n : ℤ) + 1) * S.bandOf c + n) := by
  have h0 := S.subOf_nonneg c
  have hn := S.subOf_le c
  rw [StickTiling.head, toTiling_dir, toTiling_idx, S.dirAt_gapL h, S.idxAt_gapL h, walk_SE]
  have hcast : (((n - S.subOf c).toNat + 1 : ℕ) : ℤ) = (n : ℤ) - S.subOf c + 1 := by
    push_cast
    omega
  rw [hcast]
  congr 1
  have := bandRow_mul_add n (shearRow c)
  simp only [bandOf, subOf] at *
  omega

lemma head_gapR {c : Hex} (h : S.slotAt c = .gapR) :
    S.toTiling.head c = shearCell (shearCol c) (((n : ℤ) + 1) * S.bandOf c) := by
  have h0 := S.subOf_nonneg c
  have hn := S.subOf_le c
  rw [StickTiling.head, toTiling_dir, toTiling_idx, S.dirAt_gapR h, S.idxAt_gapR h, walk_NW]
  have hcast : (((S.subOf c).toNat + 1 : ℕ) : ℤ) = S.subOf c + 1 := by
    push_cast
    omega
  rw [hcast]
  congr 1
  have := bandRow_mul_add n (shearRow c)
  simp only [bandOf, subOf] at *
  omega

lemma slotAt_head_block {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) :
    S.slotAt (S.toTiling.head c) = .block n := by
  rw [S.head_block h, slotAt_shearCell]
  exact S.slotAt_of_block h le_rfl

lemma slotAt_head_gapL {c : Hex} (h : S.slotAt c = .gapL) :
    S.slotAt (S.toTiling.head c) = .gapL := by
  rw [S.head_gapL h, slotAt_shearCell, bandRow_eq n _ _ (by positivity) le_rfl]
  exact h

lemma slotAt_head_gapR {c : Hex} (h : S.slotAt c = .gapR) :
    S.slotAt (S.toTiling.head c) = .gapR := by
  rw [S.head_gapR h, show ((n : ℤ) + 1) * S.bandOf c = ((n : ℤ) + 1) * S.bandOf c + 0 by ring,
    slotAt_shearCell, bandRow_eq n _ _ le_rfl (by positivity)]
  exact h

/-! ### The cells of a stick -/

lemma bandOf_congr {a b : Hex} (h : shearRow a = shearRow b) : S.bandOf a = S.bandOf b := by
  rw [bandOf, bandOf, h]

lemma slotAt_congr {a b : Hex} (hc : shearCol a = shearCol b) (hr : shearRow a = shearRow b) :
    S.slotAt a = S.slotAt b := by
  rw [slotAt_eq, slotAt_eq, hc, S.bandOf_congr hr]

/-- The stick through a cell of a block consists of the cells of its row lying in that block. -/
lemma mem_stickOf_block_iff {c : Hex} {j : ℕ} (h : S.slotAt c = .block j) (x : Hex) :
    x ∈ S.toTiling.stickOf c ↔
      shearRow x = shearRow c ∧ shearCol c - j ≤ shearCol x ∧ shearCol x ≤ shearCol c - j + n := by
  have hj : j ≤ n := S.slotAt_block_le h
  rw [StickTiling.mem_stickOf_iff_head_eq]
  constructor
  · intro hx
    cases hxs : S.slotAt x with
    | block k =>
      have hk : k ≤ n := S.slotAt_block_le hxs
      rw [S.head_block hxs, S.head_block h] at hx
      have h1 : shearCol x - k + n = shearCol c - j + n := by
        have := congrArg shearCol hx; simpa using this
      have h2 : shearRow x = shearRow c := by
        have := congrArg shearRow hx; simpa using this
      exact ⟨h2, by omega, by omega⟩
    | gapL =>
      exfalso
      have h1 := S.slotAt_head_gapL hxs
      rw [hx] at h1
      exact Slot.noConfusion (show Slot.gapL = Slot.block n by rw [← h1]; exact S.slotAt_head_block h)
    | gapR =>
      exfalso
      have h1 := S.slotAt_head_gapR hxs
      rw [hx] at h1
      exact Slot.noConfusion (show Slot.gapR = Slot.block n by rw [← h1]; exact S.slotAt_head_block h)
  · rintro ⟨h2, h3, h4⟩
    obtain ⟨k, hk, hkc⟩ : ∃ k : ℕ, k ≤ n ∧ shearCol x = shearCol c - j + k :=
      ⟨(shearCol x - (shearCol c - j)).toNat, by omega, by omega⟩
    have hxs : S.slotAt x = .block k := by
      rw [slotAt_eq, S.bandOf_congr h2, hkc]
      exact S.slotAt_of_block h hk
    rw [S.head_block hxs, S.head_block h, h2, hkc]
    congr 1
    omega

/-- The stick through a cell of a gap consists of the cells of its column lying in its band. -/
lemma mem_stickOf_gap_iff {c : Hex} (h : (S.slotAt c).IsGap) (x : Hex) :
    x ∈ S.toTiling.stickOf c ↔ shearCol x = shearCol c ∧ S.bandOf x = S.bandOf c := by
  have hmul : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  rw [StickTiling.mem_stickOf_iff_head_eq]
  constructor
  · intro hx
    cases hxs : S.slotAt x with
    | block k =>
      exfalso
      have h1 := S.slotAt_head_block hxs
      rw [hx] at h1
      cases hcs : S.slotAt c with
      | block _ => rw [hcs] at h; exact h.elim
      | gapL =>
        exact Slot.noConfusion (show Slot.block n = Slot.gapL by rw [← h1]; exact S.slotAt_head_gapL hcs)
      | gapR =>
        exact Slot.noConfusion (show Slot.block n = Slot.gapR by rw [← h1]; exact S.slotAt_head_gapR hcs)
    | gapL =>
      cases hcs : S.slotAt c with
      | block _ => rw [hcs] at h; exact h.elim
      | gapL =>
        rw [S.head_gapL hxs, S.head_gapL hcs] at hx
        have h1 : shearCol x = shearCol c := by have := congrArg shearCol hx; simpa using this
        have h2 : ((n : ℤ) + 1) * S.bandOf x + n = ((n : ℤ) + 1) * S.bandOf c + n := by
          have := congrArg shearRow hx; simpa using this
        exact ⟨h1, by
          have : ((n : ℤ) + 1) * S.bandOf x = ((n : ℤ) + 1) * S.bandOf c := by omega
          exact mul_left_cancel₀ (by omega) this⟩
      | gapR =>
        exfalso
        have h1 := S.slotAt_head_gapL hxs
        rw [hx] at h1
        exact Slot.noConfusion
          (show Slot.gapL = Slot.gapR by rw [← h1]; exact S.slotAt_head_gapR hcs)
    | gapR =>
      cases hcs : S.slotAt c with
      | block _ => rw [hcs] at h; exact h.elim
      | gapL =>
        exfalso
        have h1 := S.slotAt_head_gapR hxs
        rw [hx] at h1
        exact Slot.noConfusion
          (show Slot.gapR = Slot.gapL by rw [← h1]; exact S.slotAt_head_gapL hcs)
      | gapR =>
        rw [S.head_gapR hxs, S.head_gapR hcs] at hx
        have h1 : shearCol x = shearCol c := by have := congrArg shearCol hx; simpa using this
        have h2 : ((n : ℤ) + 1) * S.bandOf x = ((n : ℤ) + 1) * S.bandOf c := by
          have := congrArg shearRow hx; simpa using this
        exact ⟨h1, mul_left_cancel₀ (by omega) h2⟩
  · rintro ⟨h1, h2⟩
    have hsame : S.slotAt x = S.slotAt c := by rw [slotAt_eq, slotAt_eq, h1, h2]
    cases hcs : S.slotAt c with
    | block _ => rw [hcs] at h; exact h.elim
    | gapL =>
      rw [S.head_gapL (by rw [hsame, hcs]), S.head_gapL hcs, h1, h2]
    | gapR =>
      rw [S.head_gapR (by rw [hsame, hcs]), S.head_gapR hcs, h1, h2]

end Schematic

end StickPolyhex
