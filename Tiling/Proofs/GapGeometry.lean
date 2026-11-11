import Tiling.Proofs.SchematicRows

/-!
# The gaps of a schematic

This file isolates the combinatorics of the *gaps* of a schematic, which is what the gap
conditions of Section 2.5 of the paper talk about.

* `Schematic.GapAt S r u l m` says that the row `r` of `S` has a gap occupying the columns
  `u, …, u + l + m - 1`, whose left part (the right-facing arrows) has length `l` and whose
  right part (the left-facing arrows) has length `m`.
* `Schematic.GapData S r u l m j` adds the information that the gap sits above the column `j`
  of a block of the row below: the whole gap lies above the columns `j, …, j + l + m - 1` of a
  single block of the row `r - 1`, with `2 ≤ j` and `j + l + m ≤ n`.

The main results are the existence and uniqueness of the gap through a given gap column, the
description of the neighbours of a block (`exists_left_gap`, `exists_right_gap`), and the two
lemmas `below_gap_start` / `below_gap_end` locating the gap of the row below a block in terms of
the two gaps of its own row: if `X` is a block of the row `r`, `G₁` and `G₂` are the gaps of the
row `r` on its left and on its right, and `G'` is the gap of the row `r - 1` lying below `X`,
then the left end of `G'` is determined by `G₁` and its right end by `G₂`.
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} {S : Schematic n}

/-- `S.GapAt r u l m`: the row `r` of the schematic `S` has a gap occupying the columns
`u, …, u + l + m - 1`; its left part has length `l` and its right part has length `m`. -/
def GapAt (S : Schematic n) (r u : ℤ) (l m : ℕ) : Prop :=
  S.slot r (u - 1) = .block n ∧
  (∀ k : ℕ, k < l → S.slot r (u + k) = .gapL) ∧
  (∀ k : ℕ, k < m → S.slot r (u + l + k) = .gapR) ∧
  S.slot r (u + l + m) = .block 0

namespace GapAt

variable {r u : ℤ} {l m : ℕ}

lemma blockLeft (h : S.GapAt r u l m) : S.slot r (u - 1) = .block n := h.1

lemma slot_gapL (h : S.GapAt r u l m) {k : ℕ} (hk : k < l) : S.slot r (u + k) = .gapL :=
  h.2.1 k hk

lemma slot_gapR (h : S.GapAt r u l m) {k : ℕ} (hk : k < m) : S.slot r (u + l + k) = .gapR :=
  h.2.2.1 k hk

lemma blockRight (h : S.GapAt r u l m) : S.slot r (u + l + m) = .block 0 := h.2.2.2

lemma l_pos (h : S.GapAt r u l m) : 0 < l := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · exfalso
    subst hl
    have h1 : S.slot r u = .gapL := by
      have := S.step_of_block_n h.blockLeft
      rwa [show u - 1 + 1 = u by ring] at this
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have := h.blockRight
      simp only [Nat.cast_zero, add_zero] at this
      rw [h1] at this; exact Slot.noConfusion this
    · have := h.slot_gapR (k := 0) hm
      simp only [Nat.cast_zero, Nat.cast_zero, add_zero] at this
      rw [h1] at this; exact Slot.noConfusion this
  · exact hl

lemma m_pos (h : S.GapAt r u l m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exfalso
    subst hm
    have hl := h.l_pos
    have h1 : S.slot r (u + (l - 1 : ℕ)) = .gapL := h.slot_gapL (by omega)
    have h2 : S.slot r (u + l) = .block 0 := by
      have := h.blockRight; simpa using this
    have h3 : S.slot r (u + ((l : ℤ) - 1) + 1) = .block 0 := by
      rw [show u + ((l : ℤ) - 1) + 1 = u + l by ring]; exact h2
    have h4 := S.pred_of_block_zero h3
    rw [show ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 by omega] at h1
    rw [h1] at h4; exact Slot.noConfusion h4
  · exact hm

/-- Every column of a gap is a gap column. -/
lemma isGap (h : S.GapAt r u l m) {c : ℤ} (h0 : u ≤ c) (h1 : c < u + l + m) :
    (S.slot r c).IsGap := by
  by_cases hc : c < u + l
  · have := h.slot_gapL (k := (c - u).toNat) (by omega)
    rw [show u + ((c - u).toNat : ℤ) = c by omega] at this
    rw [this]; trivial
  · have := h.slot_gapR (k := (c - u - l).toNat) (by omega)
    rw [show u + (l : ℤ) + ((c - u - l).toNat : ℤ) = c by omega] at this
    rw [this]; trivial

/-- The two parts of a gap are determined by its starting column. -/
lemma unique {l' m' : ℕ} (h : S.GapAt r u l m) (h' : S.GapAt r u l' m') : l = l' ∧ m = m' := by
  have hsum : l + m = l' + m' := by
    by_contra hne
    rcases Nat.lt_or_ge (l + m) (l' + m') with hlt | hge
    · have h1 := h'.isGap (c := u + (l : ℤ) + m) (by omega) (by omega)
      rw [h.blockRight] at h1; exact h1
    · have hlt : l' + m' < l + m := by omega
      have h1 := h.isGap (c := u + (l' : ℤ) + m') (by omega) (by omega)
      rw [h'.blockRight] at h1; exact h1
  have hl : l = l' := by
    by_contra hne
    rcases Nat.lt_or_ge l l' with hlt | hge
    · have h1 := h.slot_gapR (k := 0) h.m_pos
      have h2 := h'.slot_gapL (k := l) hlt
      simp only [Nat.cast_zero, add_zero] at h1
      rw [h1] at h2; exact Slot.noConfusion h2
    · have hlt : l' < l := by omega
      have h1 := h'.slot_gapR (k := 0) h'.m_pos
      have h2 := h.slot_gapL (k := l') hlt
      simp only [Nat.cast_zero, add_zero] at h1
      rw [h1] at h2; exact Slot.noConfusion h2
  exact ⟨hl, by omega⟩

end GapAt

/-! ### Existence of gaps -/

/-- A gap starts just after the last column of a block. -/
lemma exists_gapAt {r u : ℤ} (h : S.slot r (u - 1) = .block n) : ∃ l m, S.GapAt r u l m := by
  have hu : S.slot r u = .gapL := by
    have := S.step_of_block_n h; rwa [show u - 1 + 1 = u by ring] at this
  have hex : ∃ N : ℕ, ¬ (S.slot r (u + N)).IsGap := by
    obtain ⟨j, hj2, hjn, hj⟩ := S.slot_overlap (r - 1) u
      (by rw [show r - 1 + 1 = r by ring, hu]; trivial)
    refine ⟨n + 1 - j, ?_⟩
    have hgL : S.slot (r - 1) (u - j + n + 1) = .gapL := S.gapL_of_block_n hj
    have hgL' : S.slot (r - 1) (u + ((n + 1 - j : ℕ) : ℤ)) = .gapL := by
      rw [show u + ((n + 1 - j : ℕ) : ℤ) = u - j + n + 1 by
        have : ((n + 1 - j : ℕ) : ℤ) = (n : ℤ) + 1 - j := by omega
        rw [this]; ring]
      exact hgL
    intro hcon
    exact S.not_isGap_above_of_isGap (r := r - 1) (y := u + ((n + 1 - j : ℕ) : ℤ))
      (by rw [hgL']; trivial) (by rw [show r - 1 + 1 = r by ring]; exact hcon)
  classical
  set k := Nat.find hex with hkdef
  have hk : ¬ (S.slot r (u + k)).IsGap := Nat.find_spec hex
  have hmin : ∀ i : ℕ, i < k → (S.slot r (u + i)).IsGap := by
    intro i hi
    by_contra hc
    have hle : k ≤ i := by rw [hkdef]; exact Nat.find_le hc
    omega
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hk
    simp only [Nat.cast_zero, add_zero] at hk
    rw [hu] at hk; exact hk trivial
  have hkblock : S.slot r (u + k) = .block 0 := by
    obtain ⟨j0, hj0⟩ := S.exists_block_of_not_isGap hk
    rcases Nat.eq_zero_or_pos j0 with h0 | hpos
    · rw [hj0, h0]
    · exfalso
      have hstep : S.slot r (u + ((k : ℤ) - 1) + 1) = .block (j0 - 1 + 1) := by
        rw [show u + ((k : ℤ) - 1) + 1 = u + k by ring, hj0]
        congr 1; omega
      have hpred := S.pred_of_block_succ hstep
      have := hmin (k - 1) (by omega)
      rw [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega] at this
      rw [hpred] at this; exact this
  have hexR : ∃ i : ℕ, S.slot r (u + i) = .gapR := by
    refine ⟨k - 1, ?_⟩
    have hstep : S.slot r (u + ((k : ℤ) - 1) + 1) = .block 0 := by
      rw [show u + ((k : ℤ) - 1) + 1 = u + k by ring]; exact hkblock
    have := S.pred_of_block_zero hstep
    rwa [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega]
  set l := Nat.find hexR with hldef
  have hlR : S.slot r (u + l) = .gapR := Nat.find_spec hexR
  have hlmin : ∀ i : ℕ, i < l → S.slot r (u + i) ≠ .gapR := by
    intro i hi
    exact Nat.find_min hexR hi
  have hlk : l < k := by
    have : l ≤ k - 1 := Nat.find_le (by
      have hstep : S.slot r (u + ((k : ℤ) - 1) + 1) = .block 0 := by
        rw [show u + ((k : ℤ) - 1) + 1 = u + k by ring]; exact hkblock
      have := S.pred_of_block_zero hstep
      rwa [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega])
    omega
  refine ⟨l, k - l, ?_, ?_, ?_, ?_⟩
  · exact h
  · intro i hi
    have hg := hmin i (by omega)
    have hne := hlmin i hi
    cases hs : S.slot r (u + i) with
    | block j => rw [hs] at hg; exact hg.elim
    | gapL => rfl
    | gapR => exact absurd hs hne
  · intro i hi
    induction i with
    | zero => simpa using hlR
    | succ p ih =>
      have hp := ih (by omega)
      have hgap : (S.slot r (u + (l : ℤ) + (p + 1 : ℕ))).IsGap := by
        have := hmin (l + (p + 1)) (by omega)
        rw [show ((l + (p + 1) : ℕ) : ℤ) = (l : ℤ) + ((p + 1 : ℕ) : ℤ) by push_cast; ring] at this
        rw [← add_assoc] at this; exact this
      have hstep := S.succ_of_gapR hp
      rw [show u + (l : ℤ) + (p : ℤ) + 1 = u + (l : ℤ) + ((p + 1 : ℕ) : ℤ) by push_cast; ring] at hstep
      rcases hstep with hR | hB
      · exact hR
      · rw [hB] at hgap; exact hgap.elim
  · rw [show u + (l : ℤ) + ((k - l : ℕ) : ℤ) = u + k by
      have : ((k - l : ℕ) : ℤ) = (k : ℤ) - l := by omega
      rw [this]; ring]
    exact hkblock

/-- Every gap column belongs to a gap. -/
lemma exists_gapAt_of_isGap {r x : ℤ} (h : (S.slot r x).IsGap) :
    ∃ (u : ℤ) (l m : ℕ), S.GapAt r u l m ∧ u ≤ x ∧ x < u + l + m := by
  classical
  have hex : ∃ t : ℕ, ¬ (S.slot r (x - (t + 1))).IsGap := by
    obtain ⟨j, hj2, hjn, hj⟩ := S.slot_overlap (r - 1) x (by rw [show r - 1 + 1 = r by ring]; exact h)
    refine ⟨j, ?_⟩
    have hgR : S.slot (r - 1) (x - j - 1) = .gapR := S.gapR_of_block hj
    intro hcon
    exact S.not_isGap_above_of_isGap (r := r - 1) (y := x - ((j : ℤ) + 1))
      (by rw [show x - ((j : ℤ) + 1) = x - j - 1 by ring, hgR]; trivial)
      (by rw [show r - 1 + 1 = r by ring]; exact hcon)
  set t := Nat.find hex with htdef
  have ht : ¬ (S.slot r (x - (t + 1))).IsGap := Nat.find_spec hex
  have hmin : ∀ i : ℕ, i ≤ t → (S.slot r (x - i)).IsGap := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simpa using h
    · by_contra hc
      have hle : t ≤ i - 1 := by
        rw [htdef]
        refine Nat.find_le ?_
        rw [show x - (((i - 1 : ℕ) : ℤ) + 1) = x - (i : ℤ) by omega]
        exact hc
      omega
  have hblock : S.slot r (x - (t + 1)) = .block n := by
    obtain ⟨j0, hj0⟩ := S.exists_block_of_not_isGap ht
    have hnext : (S.slot r (x - (t : ℤ))).IsGap := hmin t le_rfl
    rcases lt_or_eq_of_le (S.block_le hj0) with hlt | heq
    · exfalso
      have := S.step_of_block_lt hj0 hlt
      rw [show x - ((t : ℤ) + 1) + 1 = x - (t : ℤ) by ring] at this
      rw [this] at hnext; exact hnext
    · rw [hj0, heq]
  obtain ⟨l, m, hgap⟩ := exists_gapAt (u := x - (t : ℤ)) (by
    rw [show x - (t : ℤ) - 1 = x - ((t : ℤ) + 1) by ring]; exact hblock)
  refine ⟨x - (t : ℤ), l, m, hgap, by omega, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hgapcol : (S.slot r (x - (t : ℤ) + l + m)).IsGap := by
    have h1 : x - (t : ℤ) ≤ x - (t : ℤ) + l + m := by
      have : (0 : ℤ) ≤ (l : ℤ) + m := by positivity
      omega
    have := hmin (x - (x - (t : ℤ) + l + m)).toNat (by omega)
    rw [show x - (((x - (x - (t : ℤ) + (l : ℤ) + m)).toNat : ℤ)) = x - (t : ℤ) + l + m by omega] at this
    exact this
  rw [hgap.blockRight] at hgapcol
  exact hgapcol

/-- The gap that follows a block. -/
lemma exists_right_gap {r c : ℤ} (h : S.slot r c = .block 0) :
    ∃ l m, S.GapAt r (c + n + 1) l m := by
  refine exists_gapAt ?_
  rw [show c + (n : ℤ) + 1 - 1 = c + n by ring]
  have := S.slot_block_of_block (j := 0) h (k := n) le_rfl
  simpa using this

/-- The gap that precedes a block. -/
lemma exists_left_gap {r c : ℤ} (h : S.slot r c = .block 0) :
    ∃ (u : ℤ) (l m : ℕ), S.GapAt r u l m ∧ u + l + m = c := by
  have hg : (S.slot r (c - 1)).IsGap := by rw [S.gapR_of_block_zero h]; trivial
  obtain ⟨u, l, m, hgap, h1, h2⟩ := exists_gapAt_of_isGap hg
  refine ⟨u, l, m, hgap, ?_⟩
  by_contra hne
  have hc : u + l + m < c := by
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact h'
    · exact absurd (hgap.isGap (c := c) (by omega) (by omega)) (by rw [h]; exact id)
  omega

/-- There is no gap column strictly between two consecutive gaps of a row. -/
lemma gap_gap_gap {r u u' : ℤ} {l m l' m' : ℕ} (h : S.GapAt r u l m) (h' : S.GapAt r u' l' m')
    (hlt : u < u') : u + l + m + n + 1 ≤ u' := by
  by_contra hcon
  push_neg at hcon
  by_cases hcase : u' < u + l + m
  · have h1 : (S.slot r (u' - 1)).IsGap := h.isGap (by omega) (by omega)
    rw [h'.blockLeft] at h1; exact h1
  · push_neg at hcase
    have h1 : S.slot r u' = .block (u' - (u + l + m)).toNat :=
      S.slot_of_start h.blockRight hcase (by omega)
    have h2 := h'.slot_gapL (k := 0) h'.l_pos
    simp only [Nat.cast_zero, add_zero] at h2
    rw [h1] at h2; exact Slot.noConfusion h2

/-! ### The block below a gap -/

/-- `S.GapData r u l m j`: the row `r` has a gap at the columns `u, …, u + l + m - 1`, and the
column `u` lies above the column `j` of a block of the row `r - 1`. -/
def GapData (S : Schematic n) (r u : ℤ) (l m j : ℕ) : Prop :=
  S.GapAt r u l m ∧ S.slot (r - 1) u = .block j

namespace GapData

variable {r u : ℤ} {l m j : ℕ}

lemma toGapAt (h : S.GapData r u l m j) : S.GapAt r u l m := h.1

lemma slot_below (h : S.GapData r u l m j) : S.slot (r - 1) u = .block j := h.2

/-- Every column of a gap lies above a column of the same block of the row below. -/
lemma below (h : S.GapData r u l m j) {c : ℕ} (hc : c < l + m) :
    S.slot (r - 1) (u + c) = .block (j + c) := by
  induction c with
  | zero => simpa using h.slot_below
  | succ p ih =>
    have hp := ih (by omega)
    have hgap : (S.slot ((r - 1) + 1) (u + ((p + 1 : ℕ) : ℤ))).IsGap := by
      rw [show r - 1 + 1 = r by ring]
      exact h.toGapAt.isGap (by push_cast; omega) (by push_cast; omega)
    obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap (r - 1) (u + ((p + 1 : ℕ) : ℤ)) hgap
    have hjp : j + p < n := by
      by_contra hge
      have hjpn : j + p = n := by
        have := S.block_le hp; omega
      have hgL : S.slot (r - 1) (u + (p : ℤ) + 1) = .gapL := S.step_of_block_n (hjpn ▸ hp)
      rw [show u + (p : ℤ) + 1 = u + ((p + 1 : ℕ) : ℤ) by push_cast; ring, hk] at hgL
      exact Slot.noConfusion hgL
    have := S.step_of_block_lt hp hjp
    rw [show u + (p : ℤ) + 1 = u + ((p + 1 : ℕ) : ℤ) by push_cast; ring] at this
    rw [this]
    congr 1

lemma two_le (h : S.GapData r u l m j) : 2 ≤ j := by
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap (r - 1) u
    (by rw [show r - 1 + 1 = r by ring]; exact h.toGapAt.isGap le_rfl (by
      have := h.toGapAt.l_pos; have := h.toGapAt.m_pos; omega))
  rw [h.slot_below] at hk
  injection hk with e
  omega

lemma bound (h : S.GapData r u l m j) : (j : ℤ) + l + m ≤ n := by
  have hl := h.toGapAt.l_pos
  have hm := h.toGapAt.m_pos
  have hb := h.below (c := l + m - 1) (by omega)
  have hgap : (S.slot ((r - 1) + 1) (u + ((l + m - 1 : ℕ) : ℤ))).IsGap := by
    rw [show r - 1 + 1 = r by ring]
    exact h.toGapAt.isGap (by omega) (by omega)
  obtain ⟨k, hk2, hkn, hk⟩ := S.slot_overlap (r - 1) (u + ((l + m - 1 : ℕ) : ℤ)) hgap
  rw [hb] at hk
  injection hk with e
  omega

end GapData

lemma exists_gapData {r u : ℤ} {l m : ℕ} (h : S.GapAt r u l m) : ∃ j, S.GapData r u l m j := by
  obtain ⟨k, -, -, hk⟩ := S.slot_overlap (r - 1) u
    (by rw [show r - 1 + 1 = r by ring]; exact h.isGap le_rfl (by
      have := h.l_pos; have := h.m_pos; omega))
  exact ⟨k, h, hk⟩

/-! ### A block and the gap below it -/

/-- A gap of the row below a block either lies entirely below that block or is disjoint from
it. -/
lemma gap_below_subset {r c u' : ℤ} {l' m' : ℕ} (hc : S.slot r c = .block 0)
    (h' : S.GapAt (r - 1) u' l' m') (hmeet : c ≤ u' + l' + m' - 1) (hmeet' : u' ≤ c + n) :
    c ≤ u' ∧ u' + l' + m' - 1 ≤ c + n := by
  constructor
  · by_contra hcon
    push_neg at hcon
    have h1 : (S.slot (r - 1) (c - 1)).IsGap := h'.isGap (by omega) (by omega)
    have h2 : (S.slot ((r - 1) + 1) (c - 1)).IsGap := by
      rw [show r - 1 + 1 = r by ring, S.gapR_of_block_zero hc]; trivial
    exact S.not_isGap_above_of_isGap h1 h2
  · by_contra hcon
    push_neg at hcon
    have h1 : (S.slot (r - 1) (c + n + 1)).IsGap := h'.isGap (by omega) (by omega)
    have h2 : (S.slot ((r - 1) + 1) (c + n + 1)).IsGap := by
      rw [show r - 1 + 1 = r by ring]
      have := S.gapL_of_block_n (j := 0) hc
      simp only [Nat.cast_zero, sub_zero] at this
      rw [this]; trivial
    exact S.not_isGap_above_of_isGap h1 h2

/-- There is at most one gap of the row below a block lying below it. -/
lemma gap_below_unique {r c u' u'' : ℤ} {l' m' l'' m'' : ℕ}
    (h' : S.GapAt (r - 1) u' l' m') (h'' : S.GapAt (r - 1) u'' l'' m'')
    (hs' : c ≤ u') (he' : u' + l' + m' - 1 ≤ c + n)
    (hs'' : c ≤ u'') (he'' : u'' + l'' + m'' - 1 ≤ c + n) : u' = u'' := by
  have hl' := h'.l_pos; have hm' := h'.m_pos
  have hl'' := h''.l_pos; have hm'' := h''.m_pos
  rcases lt_trichotomy u' u'' with hlt | heq | hgt
  · have := gap_gap_gap h' h'' hlt
    exfalso; push_cast at this ⊢; omega
  · exact heq
  · have := gap_gap_gap h'' h' hgt
    exfalso; push_cast at this ⊢; omega

/-- The gap of the row below a block `X` starts just after the block below the gap on the left
of `X`. -/
lemma below_gap_start {r c u₁ : ℤ} {l₁ m₁ j₁ : ℕ} (hc : S.slot r c = .block 0)
    (hg : S.GapData r u₁ l₁ m₁ j₁) (he : u₁ + l₁ + m₁ = c) :
    ∃ l' m', S.GapAt (r - 1) (u₁ - j₁ + n + 1) l' m' ∧
      c ≤ u₁ - j₁ + n + 1 ∧ (u₁ - j₁ + n + 1) + l' + m' - 1 ≤ c + n := by
  have hstart : S.slot (r - 1) (u₁ - j₁) = .block 0 := S.slot_block_zero hg.slot_below
  obtain ⟨l', m', h'⟩ := exists_right_gap hstart
  have hbd := hg.bound
  have hj2 := hg.two_le
  have hle : c ≤ u₁ - j₁ + n + 1 := by omega
  have hsub := gap_below_subset hc h' (by
      have := h'.l_pos; have := h'.m_pos
      omega) (by omega)
  exact ⟨l', m', h', hle, hsub.2⟩

/-- The gap of the row below a block `X` ends just before the block below the gap on the right
of `X`. -/
lemma below_gap_end {r c : ℤ} {l₂ m₂ j₂ : ℕ} (hc : S.slot r c = .block 0)
    (hg : S.GapData r (c + n + 1) l₂ m₂ j₂) :
    ∃ (u' : ℤ) (l' m' : ℕ), S.GapAt (r - 1) u' l' m' ∧ u' + l' + m' = c + n + 1 - j₂ ∧
      c ≤ u' ∧ u' + l' + m' - 1 ≤ c + n := by
  have hstart : S.slot (r - 1) (c + n + 1 - j₂) = .block 0 := S.slot_block_zero hg.slot_below
  obtain ⟨u', l', m', h', hsum⟩ := exists_left_gap hstart
  have hbd := hg.bound
  have hj2 := hg.two_le
  have hsub := gap_below_subset hc h' (by omega) (by
      have := h'.l_pos; have := h'.m_pos
      omega)
  exact ⟨u', l', m', h', hsum, hsub.1, hsub.2⟩

/-- The gap of the row `r - 1` below a block of the row `r`: its position is determined by the
two gaps of the row `r` adjacent to that block. -/
lemma below_gap {r c u₁ : ℤ} {l₁ m₁ j₁ l₂ m₂ j₂ : ℕ} (hc : S.slot r c = .block 0)
    (hg₁ : S.GapData r u₁ l₁ m₁ j₁) (he₁ : u₁ + l₁ + m₁ = c)
    (hg₂ : S.GapData r (c + n + 1) l₂ m₂ j₂) :
    ∃ l' m', S.GapAt (r - 1) (u₁ - j₁ + n + 1) l' m' ∧
      (u₁ - j₁ + n + 1) + l' + m' = c + n + 1 - j₂ := by
  obtain ⟨l', m', h', hs', he'⟩ := below_gap_start hc hg₁ he₁
  obtain ⟨u'', l'', m'', h'', hsum'', hs'', he''⟩ := below_gap_end hc hg₂
  have : u₁ - j₁ + n + 1 = u'' := gap_below_unique h' h'' hs' he' hs'' he''
  refine ⟨l', m', h', ?_⟩
  obtain ⟨e1, e2⟩ := GapAt.unique (this ▸ h') h''
  rw [this, e1, e2]; exact hsum''

end Schematic

end StickPolyhex
