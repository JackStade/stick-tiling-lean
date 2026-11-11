import Tiling.Proofs.ABCycle

/-!
# The values realising an index tiling

This file defines the values that the construction of Sections 2.6–2.8 gives to the lines of
gaps of a column when the buckets are run through once, and proves the arithmetic facts about
them that the verification of the gap conditions needs.

For a column whose tile has index `ℓ`, the line of that column carries the value `d ℓ` at the
beginning of a cycle.  Inside a matching gadget with load function `g` it takes the four values
`d ℓ`, `d ℓ + g ℓ`, `d ℓ`, `d ℓ + 6K - g ℓ` (`ABData.mxv`), and the line of gaps to its right is
displaced by the correction `ABData.mcv`.  Inside a free gadget the value runs through
`ABData.comp1` and `ABData.exp1` (first free gadget: the `A` indices stay put and the `B` indices
are compressed into one slot and then spread out again to their new values) or through
`ABData.comp2` and `ABData.exp2` (second free gadget, with the roles of `A` and `B` exchanged).
-/

namespace StickPolyhex

namespace ABSim

/-- The displacement of the line of gaps to the right of a column at the sub-phase `i` of a
matching gadget; `ℓ` is the index of the column and `ℓ'` the index of the next one. -/
def mcorr (g : ℤ → ℤ) (ℓ ℓ' : ℤ) (i : ℕ) : ℤ :=
  if i = 2 ∨ i = 3 then g ℓ' - g ℓ else 0

namespace ABData

variable (D : ABData)

/-! ### The values of a matching gadget -/

/-- The value of the line of a column at the sub-phase `i` of a matching gadget with load
function `g`, for a column whose tile has index `ℓ`. -/
def mxv (g : ℤ → ℤ) (ℓ : ℤ) (i : ℕ) : ℤ :=
  if i = 1 then D.d * ℓ + g ℓ else if i = 3 then D.d * ℓ + 6 * D.kz - g ℓ else D.d * ℓ

/-- The number of steps of half a free gadget, as an integer. -/
lemma pz_cast : ((D.P : ℕ) : ℤ) = D.pz := rfl

/-! ### The values of the free gadgets -/

/-- The value at the `p`-th compression step of the first free gadget. -/
def comp1 (c ℓ p : ℤ) : ℤ :=
  if c % 2 = 0 then D.d * ℓ else D.d * max (D.tz + 1) (ℓ - p) + p

/-- The value at the `p`-th expansion step of the first free gadget. -/
def exp1 (c L p : ℤ) : ℤ :=
  if c % 2 = 0 then D.d * L else D.d * min L (D.tz + 1 + p) + (D.pz - p)

/-- The value at the `p`-th compression step of the second free gadget. -/
def comp2 (c L p : ℤ) : ℤ :=
  if c % 2 = 0 then D.d * min D.tz (L + p) - p else D.d * L

/-- The value at the `p`-th expansion step of the second free gadget. -/
def exp2 (c M p : ℤ) : ℤ :=
  if c % 2 = 0 then D.d * max M (D.tz - p) - (D.pz - p) else D.d * M

/-! ### All the values lie in the range of values -/

/-- A value and its mirror image both lie in the range `1, …, v`. -/
lemma slot_mem_Efull {ℓ o : ℤ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz)
    (ho1 : -(6 * D.kz + D.tz) ≤ o) (ho2 : o ≤ 6 * D.kz + D.tz) :
    D.d * ℓ + o ∈ D.Efull ∧ D.vz - (D.d * ℓ + o) ∈ D.Efull := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  refine ⟨Set.mem_Icc.2 (D.mem_range_of_slot h1 h2 ho1 ho2), ?_⟩
  have hmirror : D.vz - (D.d * ℓ + o) = D.d * (2 * D.tz + 1 - ℓ) + (-o) := by
    rw [D.vz_eq]; ring
  rw [hmirror]
  exact Set.mem_Icc.2 (D.mem_range_of_slot (by omega) (by omega) (by omega) (by omega))

/-! ### The compression and expansion values lie in the sets of the free gadgets -/

variable {D}

lemma comp1_mem {c ℓ p : ℤ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz) (hA : c % 2 = 0 → ℓ ≤ D.tz)
    (hB : ¬ c % 2 = 0 → D.tz < ℓ) (hp0 : 0 ≤ p) (hp : p ≤ D.pz) :
    D.comp1 c ℓ p ∈ D.C₁ p ∧ D.comp1 c ℓ p ∈ D.Efull ∧ D.vz - D.comp1 c ℓ p ∈ D.Efull := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  unfold comp1
  split_ifs with hc
  · have hℓ := hA hc
    have hf := D.slot_mem_Efull (ℓ := ℓ) (o := 0) h1 h2 (by omega) (by omega)
    exact ⟨⟨hp0, hp, Or.inl ⟨ℓ, h1, hℓ, rfl⟩⟩, by simpa using hf.1, by simpa using hf.2⟩
  · have hℓ := hB hc
    have hf := D.slot_mem_Efull (ℓ := max (D.tz + 1) (ℓ - p)) (o := p)
      (by omega) (by omega) (by omega) (by omega)
    exact ⟨⟨hp0, hp, Or.inr ⟨max (D.tz + 1) (ℓ - p), by omega, by omega, rfl⟩⟩, hf.1, hf.2⟩

lemma exp1_mem {c L p : ℤ} (h1 : 1 ≤ L) (h2 : L ≤ 2 * D.tz) (hA : c % 2 = 0 → L ≤ D.tz)
    (hB : ¬ c % 2 = 0 → D.tz < L) (hp0 : 0 ≤ p) (hp : p ≤ D.pz) :
    D.exp1 c L p ∈ D.D₁ p ∧ D.exp1 c L p ∈ D.Efull ∧ D.vz - D.exp1 c L p ∈ D.Efull := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  unfold exp1
  split_ifs with hc
  · have hℓ := hA hc
    have hf := D.slot_mem_Efull (ℓ := L) (o := 0) h1 h2 (by omega) (by omega)
    exact ⟨⟨hp0, hp, Or.inl ⟨L, h1, hℓ, rfl⟩⟩, by simpa using hf.1, by simpa using hf.2⟩
  · have hℓ := hB hc
    have hf := D.slot_mem_Efull (ℓ := min L (D.tz + 1 + p)) (o := D.pz - p)
      (by omega) (by omega) (by omega) (by omega)
    exact ⟨⟨hp0, hp, Or.inr ⟨min L (D.tz + 1 + p), by omega, by omega, rfl⟩⟩, hf.1, hf.2⟩

lemma comp2_mem {c L p : ℤ} (h1 : 1 ≤ L) (h2 : L ≤ 2 * D.tz) (hA : c % 2 = 0 → L ≤ D.tz)
    (hB : ¬ c % 2 = 0 → D.tz < L) (hp0 : 0 ≤ p) (hp : p ≤ D.pz) :
    D.comp2 c L p ∈ D.C₂ p ∧ D.comp2 c L p ∈ D.Efull ∧ D.vz - D.comp2 c L p ∈ D.Efull := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  unfold comp2
  split_ifs with hc
  · have hℓ := hA hc
    have hf := D.slot_mem_Efull (ℓ := min D.tz (L + p)) (o := -p)
      (by omega) (by omega) (by omega) (by omega)
    refine ⟨⟨hp0, hp, Or.inr ⟨min D.tz (L + p), by omega, by omega, by ring⟩⟩, ?_, ?_⟩
    · have : D.d * min D.tz (L + p) - p = D.d * min D.tz (L + p) + -p := by ring
      rw [this]; exact hf.1
    · have : D.d * min D.tz (L + p) - p = D.d * min D.tz (L + p) + -p := by ring
      rw [this]; exact hf.2
  · have hℓ := hB hc
    have hf := D.slot_mem_Efull (ℓ := L) (o := 0) h1 h2 (by omega) (by omega)
    exact ⟨⟨hp0, hp, Or.inl ⟨L, by omega, h2, rfl⟩⟩, by simpa using hf.1, by simpa using hf.2⟩

lemma exp2_mem {c M p : ℤ} (h1 : 1 ≤ M) (h2 : M ≤ 2 * D.tz) (hA : c % 2 = 0 → M ≤ D.tz)
    (hB : ¬ c % 2 = 0 → D.tz < M) (hp0 : 0 ≤ p) (hp : p ≤ D.pz) :
    D.exp2 c M p ∈ D.D₂ p ∧ D.exp2 c M p ∈ D.Efull ∧ D.vz - D.exp2 c M p ∈ D.Efull := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  unfold exp2
  split_ifs with hc
  · have hℓ := hA hc
    have hf := D.slot_mem_Efull (ℓ := max M (D.tz - p)) (o := -(D.pz - p))
      (by omega) (by omega) (by omega) (by omega)
    refine ⟨⟨hp0, hp, Or.inr ⟨max M (D.tz - p), by omega, by omega, by ring⟩⟩, ?_, ?_⟩
    · have : D.d * max M (D.tz - p) - (D.pz - p) = D.d * max M (D.tz - p) + -(D.pz - p) := by ring
      rw [this]; exact hf.1
    · have : D.d * max M (D.tz - p) - (D.pz - p) = D.d * max M (D.tz - p) + -(D.pz - p) := by ring
      rw [this]; exact hf.2
  · have hℓ := hB hc
    have hf := D.slot_mem_Efull (ℓ := M) (o := 0) h1 h2 (by omega) (by omega)
    exact ⟨⟨hp0, hp, Or.inl ⟨M, by omega, h2, rfl⟩⟩, by simpa using hf.1, by simpa using hf.2⟩

/-! ### The steps between consecutive values of a free gadget -/

lemma comp1_step {c ℓ p : ℤ} (hB : ¬ c % 2 = 0 → D.tz < ℓ) :
    -D.d + 1 ≤ D.comp1 c ℓ (p + 1) - D.comp1 c ℓ p ∧
      D.comp1 c ℓ (p + 1) - D.comp1 c ℓ p ≤ 1 := by
  have hd := D.d_pos
  unfold comp1
  split_ifs with hc
  · omega
  · have hℓ := hB hc
    have hmax : max (D.tz + 1) (ℓ - (p + 1)) = max (D.tz + 1) (ℓ - p) ∨
        D.d * max (D.tz + 1) (ℓ - (p + 1)) + D.d = D.d * max (D.tz + 1) (ℓ - p) := by
      rcases le_or_gt (ℓ - p) (D.tz + 1) with h | h
      · left; omega
      · right
        have : max (D.tz + 1) (ℓ - p) = max (D.tz + 1) (ℓ - (p + 1)) + 1 := by omega
        rw [this]; ring
    rcases hmax with h | h
    · rw [h]; omega
    · omega

lemma exp1_step {c L p : ℤ} :
    -1 ≤ D.exp1 c L (p + 1) - D.exp1 c L p ∧
      D.exp1 c L (p + 1) - D.exp1 c L p ≤ D.d - 1 := by
  have hd := D.d_pos
  unfold exp1
  split_ifs with hc
  · omega
  · have hmin : min L (D.tz + 1 + (p + 1)) = min L (D.tz + 1 + p) ∨
        D.d * min L (D.tz + 1 + (p + 1)) = D.d * min L (D.tz + 1 + p) + D.d := by
      rcases le_or_gt L (D.tz + 1 + p) with h | h
      · left; omega
      · right
        have : min L (D.tz + 1 + (p + 1)) = min L (D.tz + 1 + p) + 1 := by omega
        rw [this]; ring
    rcases hmin with h | h
    · rw [h]; omega
    · omega

lemma comp2_step {c L p : ℤ} :
    -1 ≤ D.comp2 c L (p + 1) - D.comp2 c L p ∧
      D.comp2 c L (p + 1) - D.comp2 c L p ≤ D.d - 1 := by
  have hd := D.d_pos
  unfold comp2
  split_ifs with hc
  · have hmin : min D.tz (L + (p + 1)) = min D.tz (L + p) ∨
        D.d * min D.tz (L + (p + 1)) = D.d * min D.tz (L + p) + D.d := by
      rcases le_or_gt D.tz (L + p) with h | h
      · left; omega
      · right
        have : min D.tz (L + (p + 1)) = min D.tz (L + p) + 1 := by omega
        rw [this]; ring
    rcases hmin with h | h
    · rw [h]; omega
    · omega
  · omega

lemma exp2_step {c M p : ℤ} :
    -D.d + 1 ≤ D.exp2 c M (p + 1) - D.exp2 c M p ∧
      D.exp2 c M (p + 1) - D.exp2 c M p ≤ 1 := by
  have hd := D.d_pos
  unfold exp2
  split_ifs with hc
  · have hmax : max M (D.tz - (p + 1)) = max M (D.tz - p) ∨
        D.d * max M (D.tz - (p + 1)) + D.d = D.d * max M (D.tz - p) := by
      rcases le_or_gt (D.tz - p) M with h | h
      · left; omega
      · right
        have : max M (D.tz - p) = max M (D.tz - (p + 1)) + 1 := by omega
        rw [this]; ring
    rcases hmax with h | h
    · rw [h]; omega
    · omega
  · omega

/-! ### The junctions between the gadgets -/

lemma comp1_zero {c ℓ : ℤ} (hB : ¬ c % 2 = 0 → D.tz < ℓ) : D.comp1 c ℓ 0 = D.d * ℓ := by
  unfold comp1
  split_ifs with hc
  · rfl
  · have := hB hc
    rw [show max (D.tz + 1) (ℓ - 0) = ℓ by omega]
    ring

lemma exp1_top {c L : ℤ} (h2 : L ≤ 2 * D.tz) : D.exp1 c L D.pz = D.d * L := by
  have := D.tz_le_pz_add_one
  unfold exp1
  split_ifs with hc
  · rfl
  · rw [show min L (D.tz + 1 + D.pz) = L by omega]
    ring

lemma comp2_zero {c L : ℤ} (hA : c % 2 = 0 → L ≤ D.tz) : D.comp2 c L 0 = D.d * L := by
  unfold comp2
  split_ifs with hc
  · have := hA hc
    rw [show min D.tz (L + 0) = L by omega]
    ring
  · rfl

lemma exp2_top {c M : ℤ} (h1 : 1 ≤ M) : D.exp2 c M D.pz = D.d * M := by
  have := D.tz_le_pz_add_one
  unfold exp2
  split_ifs with hc
  · rw [show max M (D.tz - D.pz) = M by omega]
    ring
  · rfl

/-- The step from the end of the compression half of the first free gadget to the beginning of
its expansion half. -/
lemma comp1_exp1_step {c ℓ L : ℤ} (hB : ¬ c % 2 = 0 → D.tz < ℓ) (hB' : ¬ c % 2 = 0 → D.tz < L)
    (hA : c % 2 = 0 → L = ℓ) (h2 : ℓ ≤ 2 * D.tz) :
    -1 ≤ D.exp1 c L 1 - D.comp1 c ℓ D.pz ∧ D.exp1 c L 1 - D.comp1 c ℓ D.pz ≤ D.d - 1 := by
  have hd := D.d_pos
  have ht := D.one_le_tz
  have hpt := D.tz_le_pz_add_one
  unfold exp1 comp1
  split_ifs with hc
  · rw [hA hc]; omega
  · have h1 := hB hc
    have h1' := hB' hc
    rw [show max (D.tz + 1) (ℓ - D.pz) = D.tz + 1 by omega]
    have hmin : min L (D.tz + 1 + 1) = D.tz + 1 ∨ min L (D.tz + 1 + 1) = D.tz + 2 := by omega
    rcases hmin with h | h <;> rw [h] <;> [skip; rw [show D.tz + 2 = (D.tz + 1) + 1 by ring,
      mul_add, mul_one]] <;> omega

/-- The step from the end of the compression half of the second free gadget to the beginning of
its expansion half. -/
lemma comp2_exp2_step {c L M : ℤ} (hA : c % 2 = 0 → L ≤ D.tz) (hA' : c % 2 = 0 → M ≤ D.tz)
    (hB : ¬ c % 2 = 0 → M = L) (h1 : 1 ≤ L) :
    -D.d + 1 ≤ D.exp2 c M 1 - D.comp2 c L D.pz ∧ D.exp2 c M 1 - D.comp2 c L D.pz ≤ 1 := by
  have hd := D.d_pos
  have ht := D.one_le_tz
  have hpt := D.tz_le_pz_add_one
  unfold exp2 comp2
  split_ifs with hc
  · have hl := hA hc
    have hm := hA' hc
    rw [show min D.tz (L + D.pz) = D.tz by omega]
    have hmax : max M (D.tz - 1) = D.tz - 1 ∨ max M (D.tz - 1) = D.tz := by omega
    rcases hmax with h | h <;> rw [h] <;> [rw [show D.tz - 1 = D.tz + (-1) by ring, mul_add]; skip]
      <;> omega
  · rw [hB hc]; omega

lemma one_le_P : 1 ≤ D.P := by unfold P; omega

lemma pz_bound {p : ℕ} (h : p ≤ D.P) : (0 : ℤ) ≤ (p : ℤ) ∧ (p : ℤ) ≤ D.pz :=
  ⟨Int.natCast_nonneg p, by rw [← D.pz_cast]; exact_mod_cast h⟩

lemma mxv_zero (g : ℤ → ℤ) (ℓ : ℤ) : D.mxv g ℓ 0 = D.d * ℓ := by unfold mxv; norm_num

lemma mxv_four (g : ℤ → ℤ) (ℓ : ℤ) : D.mxv g ℓ 4 = D.d * ℓ := by unfold mxv; norm_num

/-! ### The alternation set of a matching gadget -/

/-- The value of the line to the right of a column in the middle of a matching gadget whose load
function has base `2K` on the `A` indices: it lies in the alternation set as soon as the kinds of
the two indices alternate and, when the left one is an `A` index, the colors agree. -/
lemma Aset_of_match {g h : ℤ → ℤ} {ℓ ℓ' : ℤ} (hh : ∀ x, 0 ≤ h x ∧ h x < D.kz)
    (hg : ∀ x, g x = (if x ≤ D.tz then 2 * D.kz else 4 * D.kz) + h x)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz)
    (halt : (ℓ ≤ D.tz ∧ ¬ ℓ' ≤ D.tz ∧ h ℓ = h ℓ') ∨ (¬ ℓ ≤ D.tz ∧ ℓ' ≤ D.tz)) :
    D.vz - D.d * ℓ + (g ℓ' - g ℓ) ∈ D.Aset := by
  have hk := D.one_le_kz
  have hslot : D.vz - D.d * ℓ = D.d * (2 * D.tz + 1 - ℓ) := by rw [D.vz_eq]; ring
  have hj1 : 1 ≤ 2 * D.tz + 1 - ℓ := by omega
  have hj2 : 2 * D.tz + 1 - ℓ ≤ 2 * D.tz := by omega
  rw [hslot]
  rcases halt with ⟨ha, ha', hcol⟩ | ⟨ha, ha'⟩
  · refine ⟨2 * D.tz + 1 - ℓ, hj1, hj2, Or.inl ?_⟩
    rw [hg ℓ, hg ℓ', if_pos ha, if_neg ha', hcol]
    ring
  · refine ⟨2 * D.tz + 1 - ℓ, hj1, hj2, Or.inr ⟨h ℓ' - h ℓ, ?_, ?_, ?_⟩⟩
    · have := hh ℓ; have := hh ℓ'; omega
    · have := hh ℓ; have := hh ℓ'; omega
    · rw [hg ℓ, hg ℓ', if_neg ha, if_pos ha']
      ring

/-- The mirrored form of `ABData.Aset_of_match`, for a load function with base `4K` on the `A`
indices. -/
lemma Aset_of_match' {g h : ℤ → ℤ} {ℓ ℓ' : ℤ} (hh : ∀ x, 0 ≤ h x ∧ h x < D.kz)
    (hg : ∀ x, g x = (if x ≤ D.tz then 4 * D.kz else 2 * D.kz) + h x)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz)
    (halt : (ℓ ≤ D.tz ∧ ¬ ℓ' ≤ D.tz) ∨ (¬ ℓ ≤ D.tz ∧ ℓ' ≤ D.tz ∧ h ℓ = h ℓ')) :
    D.vz - D.d * ℓ + (g ℓ' - g ℓ) ∈ D.Aset := by
  have hk := D.one_le_kz
  have hslot : D.vz - D.d * ℓ = D.d * (2 * D.tz + 1 - ℓ) := by rw [D.vz_eq]; ring
  have hj1 : 1 ≤ 2 * D.tz + 1 - ℓ := by omega
  have hj2 : 2 * D.tz + 1 - ℓ ≤ 2 * D.tz := by omega
  rw [hslot]
  rcases halt with ⟨ha, ha'⟩ | ⟨ha, ha', hcol⟩
  · refine ⟨2 * D.tz + 1 - ℓ, hj1, hj2, Or.inr ⟨h ℓ' - h ℓ, ?_, ?_, ?_⟩⟩
    · have := hh ℓ; have := hh ℓ'; omega
    · have := hh ℓ; have := hh ℓ'; omega
    · rw [hg ℓ, hg ℓ', if_pos ha, if_neg ha']
      ring
  · refine ⟨2 * D.tz + 1 - ℓ, hj1, hj2, Or.inl ?_⟩
    rw [hg ℓ, hg ℓ', if_neg ha, if_pos ha', hcol]
    ring

lemma g₁_eq (ℓ : ℤ) : D.g₁ ℓ = (if ℓ ≤ D.tz then 2 * D.kz else 4 * D.kz) + D.h₁ ℓ := rfl

lemma g₂_eq (ℓ : ℤ) : D.g₂ ℓ = (if ℓ ≤ D.tz then 4 * D.kz else 2 * D.kz) + D.h₂ ℓ := rfl

lemma g₃_eq (ℓ : ℤ) : D.g₃ ℓ = (if ℓ ≤ D.tz then 2 * D.kz else 4 * D.kz) + D.h₃ ℓ := rfl

lemma g₄_eq (ℓ : ℤ) : D.g₄ ℓ = (if ℓ ≤ D.tz then 4 * D.kz else 2 * D.kz) + D.h₄ ℓ := rfl

/-! ### Memberships inside a matching gadget -/

/-- The value of the line of a column at the sub-phase `0`, `2` or `4` of a matching gadget lies
in the encoding set, and so does the value of the mirrored line. -/
lemma mxv_mem_Eset {g : ℤ → ℤ} {ℓ : ℤ} {i : ℕ} (hi : i = 0 ∨ i = 2 ∨ i = 4)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz) :
    D.mxv g ℓ i = D.d * ℓ ∧ D.mxv g ℓ i ∈ D.Eset ∧ D.vz - D.mxv g ℓ i ∈ D.Eset := by
  have hval : D.mxv g ℓ i = D.d * ℓ := by
    unfold mxv; rcases hi with rfl | rfl | rfl <;> norm_num
  refine ⟨hval, by rw [hval]; exact ⟨ℓ, h1, h2, rfl⟩, ?_⟩
  rw [hval, show D.vz - D.d * ℓ = D.d * (2 * D.tz + 1 - ℓ) by rw [D.vz_eq]; ring]
  exact ⟨2 * D.tz + 1 - ℓ, by omega, by omega, rfl⟩

/-- The value of the line of a column at the sub-phase `1` of a matching gadget. -/
lemma mxv_mem_Rload {g : ℤ → ℤ} {ℓ : ℤ} (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz) :
    D.mxv g ℓ 1 = D.d * ℓ + g ℓ ∧ D.mxv g ℓ 1 ∈ D.Rload g ∧
      D.vz - D.mxv g ℓ 1 ∈ D.Efull := by
  have hk := D.one_le_kz
  have hb := hgb ℓ
  have hval : D.mxv g ℓ 1 = D.d * ℓ + g ℓ := by unfold mxv; norm_num
  refine ⟨hval, by rw [hval]; exact ⟨ℓ, h1, h2, rfl⟩, ?_⟩
  rw [hval]
  exact (D.slot_mem_Efull h1 h2 (by omega) (by omega)).2

/-- The value of the line of a column at the sub-phase `3` of a matching gadget. -/
lemma mxv_mem_Rreset {g : ℤ → ℤ} {ℓ : ℤ}
    (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz) :
    D.mxv g ℓ 3 = D.d * ℓ + 6 * D.kz - g ℓ ∧ D.mxv g ℓ 3 ∈ D.Rreset := by
  have hk := D.one_le_kz
  have hb := hgb ℓ
  have hval : D.mxv g ℓ 3 = D.d * ℓ + 6 * D.kz - g ℓ := by unfold mxv; norm_num
  refine ⟨hval, ?_⟩
  rw [hval]
  exact ⟨ℓ, h1, h2, 6 * D.kz - g ℓ, by omega, by omega, by ring⟩

end ABData

end ABSim

end StickPolyhex
