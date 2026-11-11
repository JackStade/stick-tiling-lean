import Tiling.Proofs.ABGapSpec

/-!
# The arithmetic of the gadgets

This file contains the purely arithmetical content of Sections 2.6–2.8: what the sets of the
bucket table force on the value of a single line of gaps as it moves from one row to the next.

* `ABData.load_forced` and `ABData.unload_forced` force the first two steps of a
  matching gadget. `ABData.reset_forced` shows that the last two steps preserve the
  encoded index even though the third-state offset is not uniquely determined.
* `ABData.Aset_offset` is the heart of the matching gadget: the set of right values allowed in
  its second bucket only permits the offsets `2K` (with no color difference) and `-2K + e` with
  `|e| < K`.  `ABData.matchA_concl` and `ABData.matchB_concl` turn this into the statement that
  the kinds of two adjacent indices alternate and that the colors agree across the boundaries of
  one of the two directions.
* `ABData.C₁_step`, `ABData.D₁_step`, `ABData.C₂_step`, `ABData.D₂_step` are the steps of the two
  free gadgets: the locked family of indices does not move at all, and the free family stays
  free.
-/

namespace StickPolyhex

namespace ABSim

namespace ABData

variable (D : ABData)

/-! ### Two monotonicity helpers -/

lemma dmul_le {a b : ℤ} (h : a ≤ b) : D.d * a ≤ D.d * b :=
  mul_le_mul_of_nonneg_left h (le_of_lt D.d_pos)

lemma dmul_eq_of_le {a b : ℤ} (h : a + 1 ≤ b) : D.d * a + D.d ≤ D.d * b := by
  have := D.dmul_le h
  have h2 : D.d * (a + 1) = D.d * a + D.d := by ring
  omega

/-! ### The encoding set -/

/-- An `A` index: one of the values `d, 2d, …, t d`. -/
def isA (u : ℤ) : Prop := ∃ ℓ : ℤ, 1 ≤ ℓ ∧ ℓ ≤ D.tz ∧ u = D.d * ℓ

/-- A `B` index: one of the values `(t+1) d, …, 2t d`. -/
def isB (u : ℤ) : Prop := ∃ ℓ : ℤ, D.tz + 1 ≤ ℓ ∧ ℓ ≤ 2 * D.tz ∧ u = D.d * ℓ

lemma isA_or_isB {u : ℤ} (h : u ∈ D.Eset) : D.isA u ∨ D.isB u := by
  obtain ⟨ℓ, h1, h2, rfl⟩ := h
  rcases le_or_gt ℓ D.tz with hl | hl
  · exact Or.inl ⟨ℓ, h1, hl, rfl⟩
  · exact Or.inr ⟨ℓ, by omega, h2, rfl⟩

lemma isA_mem_Eset {u : ℤ} (h : D.isA u) : u ∈ D.Eset := by
  obtain ⟨ℓ, h1, h2, rfl⟩ := h
  have := D.one_le_tz
  exact ⟨ℓ, h1, by omega, rfl⟩

lemma isB_mem_Eset {u : ℤ} (h : D.isB u) : u ∈ D.Eset := by
  obtain ⟨ℓ, h1, h2, rfl⟩ := h
  have := D.one_le_tz
  exact ⟨ℓ, by omega, h2, rfl⟩

lemma not_isA_isB {u : ℤ} (hA : D.isA u) (hB : D.isB u) : False := by
  obtain ⟨ℓ, h1, h2, rfl⟩ := hA
  obtain ⟨ℓ', h1', h2', he⟩ := hB
  have hdp := D.d_pos
  have e : D.d * ℓ + 0 = D.d * ℓ' + 0 := by omega
  obtain ⟨hll, -⟩ := D.slot_unique e (by omega) (by omega)
  omega

/-! ### The four steps of a matching gadget -/

lemma load_forced {g : ℤ → ℤ} (hg : ∀ ℓ, 2 * D.kz ≤ g ℓ ∧ g ℓ ≤ 5 * D.kz - 1) {ℓ x' : ℤ}
    (hx' : x' ∈ D.Rload g) (h0 : 0 ≤ x' - D.d * ℓ) (h6 : x' - D.d * ℓ ≤ 6 * D.kz) :
    x' = D.d * ℓ + g ℓ := by
  obtain ⟨m, _, _, rfl⟩ := hx'
  have hgm := hg m
  have hk := D.one_le_kz
  have hd := D.d_big
  have heq : D.d * m + g m = D.d * ℓ + (D.d * m + g m - D.d * ℓ) := by ring
  obtain ⟨hml, _⟩ := D.slot_unique heq (by omega) (by omega)
  subst hml
  ring

lemma unload_forced {g : ℤ → ℤ} (hg : ∀ ℓ, 2 * D.kz ≤ g ℓ ∧ g ℓ ≤ 5 * D.kz - 1) {ℓ x'' : ℤ}
    (hx'' : x'' ∈ D.Eset) (h0 : 0 ≤ D.d * ℓ + g ℓ - x'') (h6 : D.d * ℓ + g ℓ - x'' ≤ 6 * D.kz) :
    x'' = D.d * ℓ := by
  obtain ⟨m, _, _, rfl⟩ := hx''
  have hgl := hg ℓ
  have hk := D.one_le_kz
  have hd := D.d_big
  have heq : D.d * m + 0 = D.d * ℓ + (D.d * m - D.d * ℓ) := by ring
  obtain ⟨hml, _⟩ := D.slot_unique heq (by omega) (by omega)
  subst hml
  ring

/-- Two steps bounded by `6K` cannot change the encoded index; no particular
intermediate value is required. -/
lemma reset_forced {ℓ u x : ℤ} (hx : x ∈ D.Eset)
    (hu0 : 0 ≤ u - D.d * ℓ) (hu6 : u - D.d * ℓ ≤ 6 * D.kz)
    (hx0 : 0 ≤ u - x) (hx6 : u - x ≤ 6 * D.kz) : x = D.d * ℓ := by
  obtain ⟨m, _, _, rfl⟩ := hx
  have hd := D.d_big
  have hk := D.one_le_kz
  have heq : D.d * m + 0 = D.d * ℓ + (D.d * m - D.d * ℓ) := by ring
  obtain ⟨hml, _⟩ := D.slot_unique heq (by omega) (by omega)
  rw [hml]

/-! ### The alternation set -/

/-- The offsets from a multiple of `d` permitted by the set `Aset`: either exactly `2K`, or at
most `-K-1`.  This is what makes a matching gadget forbid two adjacent indices of the same kind
and force the colors to agree in one of the two directions. -/
lemma Aset_offset {j Δ : ℤ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2 * D.tz)
    (hΔ1 : -(3 * D.kz) < Δ) (hΔ2 : Δ < 3 * D.kz) (h : D.d * j + Δ ∈ D.Aset) :
    Δ = 2 * D.kz ∨ Δ ≤ -D.kz - 1 := by
  obtain ⟨m, _, _, hcase⟩ := h
  have hk := D.one_le_kz
  have hd := D.d_big
  rcases hcase with heq | ⟨e, he1, he2, heq⟩
  · have heq' : D.d * j + Δ = D.d * m + 2 * D.kz := heq
    obtain ⟨hjm, hoff⟩ := D.slot_unique heq' (by omega) (by omega)
    exact Or.inl (by omega)
  · have heq' : D.d * j + Δ = D.d * m + (-(2 * D.kz) + e) := by rw [heq]; ring
    obtain ⟨hjm, hoff⟩ := D.slot_unique heq' (by omega) (by omega)
    exact Or.inr (by omega)

/-- The conclusion of a matching gadget whose load function has base `2K` on the `A` indices: the
kinds of two adjacent indices alternate, and the colors agree across every boundary going from an
`A` index to a `B` index. -/
lemma matchA_concl {h : ℤ → ℤ} (hh : ∀ ℓ, 0 ≤ h ℓ ∧ h ℓ < D.kz) {ℓ ℓ' : ℤ}
    (hd : ((if ℓ' ≤ D.tz then 2 * D.kz else 4 * D.kz) + h ℓ') -
      ((if ℓ ≤ D.tz then 2 * D.kz else 4 * D.kz) + h ℓ) = 2 * D.kz ∨
      ((if ℓ' ≤ D.tz then 2 * D.kz else 4 * D.kz) + h ℓ') -
      ((if ℓ ≤ D.tz then 2 * D.kz else 4 * D.kz) + h ℓ) ≤ -D.kz - 1) :
    (ℓ ≤ D.tz ↔ ¬ ℓ' ≤ D.tz) ∧ (ℓ ≤ D.tz → h ℓ = h ℓ') := by
  have h1 := hh ℓ
  have h2 := hh ℓ'
  have hk := D.one_le_kz
  by_cases hA : ℓ ≤ D.tz <;> by_cases hA' : ℓ' ≤ D.tz
  · rw [if_pos hA, if_pos hA'] at hd; exact absurd hd (by omega)
  · rw [if_pos hA, if_neg hA'] at hd
    exact ⟨⟨fun _ => hA', fun _ => hA⟩, fun _ => by omega⟩
  · rw [if_neg hA, if_pos hA'] at hd
    exact ⟨⟨fun h => absurd h hA, fun h => absurd hA' h⟩, fun h => absurd h hA⟩
  · rw [if_neg hA, if_neg hA'] at hd; exact absurd hd (by omega)

/-- The conclusion of a matching gadget whose load function has base `4K` on the `A` indices: the
kinds alternate, and the colors agree across every boundary going from a `B` index to an `A`
index. -/
lemma matchB_concl {h : ℤ → ℤ} (hh : ∀ ℓ, 0 ≤ h ℓ ∧ h ℓ < D.kz) {ℓ ℓ' : ℤ}
    (hd : ((if ℓ' ≤ D.tz then 4 * D.kz else 2 * D.kz) + h ℓ') -
      ((if ℓ ≤ D.tz then 4 * D.kz else 2 * D.kz) + h ℓ) = 2 * D.kz ∨
      ((if ℓ' ≤ D.tz then 4 * D.kz else 2 * D.kz) + h ℓ') -
      ((if ℓ ≤ D.tz then 4 * D.kz else 2 * D.kz) + h ℓ) ≤ -D.kz - 1) :
    (ℓ ≤ D.tz ↔ ¬ ℓ' ≤ D.tz) ∧ (¬ ℓ ≤ D.tz → h ℓ = h ℓ') := by
  have h1 := hh ℓ
  have h2 := hh ℓ'
  have hk := D.one_le_kz
  by_cases hA : ℓ ≤ D.tz <;> by_cases hA' : ℓ' ≤ D.tz
  · rw [if_pos hA, if_pos hA'] at hd; exact absurd hd (by omega)
  · rw [if_pos hA, if_neg hA'] at hd
    exact ⟨⟨fun _ => hA', fun _ => hA⟩, fun h => absurd hA h⟩
  · rw [if_neg hA, if_pos hA'] at hd
    exact ⟨⟨fun h => absurd h hA, fun h => absurd hA' h⟩, fun _ => by omega⟩
  · rw [if_neg hA, if_neg hA'] at hd; exact absurd hd (by omega)

/-! ### The ends of the free gadgets -/

lemma C₁_zero : D.C₁ 0 = D.Eset := by
  have ht := D.one_le_tz
  have hp := D.one_le_pz
  ext u
  constructor
  · rintro ⟨-, -, ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩⟩
    · exact ⟨ℓ, h1, by omega, rfl⟩
    · exact ⟨ℓ, by omega, by omega, by ring⟩
  · rintro ⟨ℓ, h1, h2, rfl⟩
    refine ⟨le_refl 0, by omega, ?_⟩
    rcases le_or_gt ℓ D.tz with hl | hl
    · exact Or.inl ⟨ℓ, h1, hl, rfl⟩
    · exact Or.inr ⟨ℓ, by omega, by omega, by ring⟩

lemma D₁_top : D.D₁ D.pz = D.Eset := by
  have ht := D.one_le_tz
  have hp := D.tz_le_pz_add_one
  have hp' := D.pz_le_tz
  ext u
  constructor
  · rintro ⟨-, -, ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩⟩
    · exact ⟨ℓ, h1, by omega, rfl⟩
    · exact ⟨ℓ, by omega, by omega, by ring⟩
  · rintro ⟨ℓ, h1, h2, rfl⟩
    refine ⟨by omega, le_refl _, ?_⟩
    rcases le_or_gt ℓ D.tz with hl | hl
    · exact Or.inl ⟨ℓ, h1, hl, rfl⟩
    · exact Or.inr ⟨ℓ, by omega, by omega, by ring⟩

lemma C₂_zero : D.C₂ 0 = D.Eset := by
  have ht := D.one_le_tz
  have hp := D.one_le_pz
  ext u
  constructor
  · rintro ⟨-, -, ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩⟩
    · exact ⟨ℓ, by omega, h2, rfl⟩
    · exact ⟨ℓ, by omega, by omega, by ring⟩
  · rintro ⟨ℓ, h1, h2, rfl⟩
    refine ⟨le_refl 0, by omega, ?_⟩
    rcases le_or_gt ℓ D.tz with hl | hl
    · exact Or.inr ⟨ℓ, by omega, hl, by ring⟩
    · exact Or.inl ⟨ℓ, by omega, h2, rfl⟩

lemma D₂_top : D.D₂ D.pz = D.Eset := by
  have ht := D.one_le_tz
  have hp := D.tz_le_pz_add_one
  have hp' := D.pz_le_tz
  ext u
  constructor
  · rintro ⟨-, -, ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩⟩
    · exact ⟨ℓ, by omega, h2, rfl⟩
    · exact ⟨ℓ, by omega, by omega, by ring⟩
  · rintro ⟨ℓ, h1, h2, rfl⟩
    refine ⟨by omega, le_refl _, ?_⟩
    rcases le_or_gt ℓ D.tz with hl | hl
    · exact Or.inr ⟨ℓ, by omega, hl, by ring⟩
    · exact Or.inl ⟨ℓ, by omega, h2, rfl⟩

/-- The compression half and the expansion half of the first free gadget meet in the middle. -/
lemma C₁_top_eq_D₁_zero : D.C₁ D.pz = D.D₁ 0 := by
  have ht := D.one_le_tz
  have hp := D.tz_le_pz_add_one
  have hp' := D.pz_le_tz
  have h1 : max (D.tz + 1) (2 * D.tz - D.pz) = D.tz + 1 := by omega
  have h2 : min (2 * D.tz) (D.tz + 1 + 0) = D.tz + 1 := by omega
  ext u
  constructor
  · rintro ⟨-, -, h | ⟨ℓ, ha, hb, rfl⟩⟩
    · exact ⟨le_refl 0, by omega, Or.inl h⟩
    · rw [h1] at hb
      exact ⟨le_refl 0, by omega, Or.inr ⟨ℓ, ha, by omega, by ring⟩⟩
  · rintro ⟨-, -, h | ⟨ℓ, ha, hb, rfl⟩⟩
    · exact ⟨by omega, le_refl _, Or.inl h⟩
    · rw [h2] at hb
      exact ⟨by omega, le_refl _, Or.inr ⟨ℓ, ha, by omega, by ring⟩⟩

/-- The compression half and the expansion half of the second free gadget meet in the middle. -/
lemma C₂_top_eq_D₂_zero : D.C₂ D.pz = D.D₂ 0 := by
  have ht := D.one_le_tz
  have hp := D.tz_le_pz_add_one
  have hp' := D.pz_le_tz
  have h1 : min D.tz (1 + D.pz) = D.tz := by omega
  have h2 : max 1 (D.tz - 0) = D.tz := by omega
  ext u
  constructor
  · rintro ⟨-, -, h | ⟨ℓ, ha, hb, rfl⟩⟩
    · exact ⟨le_refl 0, by omega, Or.inl h⟩
    · rw [h1] at ha
      exact ⟨le_refl 0, by omega, Or.inr ⟨ℓ, by omega, hb, by ring⟩⟩
  · rintro ⟨-, -, h | ⟨ℓ, ha, hb, rfl⟩⟩
    · exact ⟨by omega, le_refl _, Or.inl h⟩
    · rw [h2] at ha
      exact ⟨by omega, le_refl _, Or.inr ⟨ℓ, by omega, hb, by ring⟩⟩

/-! ### The steps of the free gadgets -/

/-- A compression step of the first free gadget: the `A` indices do not move, and a value which
is not an `A` index cannot become one. -/
lemma C₁_step {p u u' : ℤ} (hp1 : 1 ≤ p)
    (hu : u ∈ D.C₁ (p - 1)) (hu' : u' ∈ D.C₁ p) (h1 : -D.d + 1 ≤ u' - u) (h2 : u' - u ≤ 1) :
    (D.isA u → u' = u) ∧ (D.isA u' → D.isA u) := by
  have ht := D.one_le_tz
  have hdp := D.d_pos
  have hpt := D.pz_le_tz
  have hdt := D.d_big
  obtain ⟨-, -, hu⟩ := hu
  obtain ⟨-, -, hu'⟩ := hu'
  constructor
  · rintro ⟨ℓ, hl1, hl2, rfl⟩
    rcases hu' with ⟨ℓ', h1', h2', rfl⟩ | ⟨ℓ', h1', h2', rfl⟩
    · have e1 : D.d * ℓ' + 0 = D.d * ℓ + (D.d * ℓ' - D.d * ℓ) := by ring
      obtain ⟨he, -⟩ := D.slot_unique e1 (by omega) (by omega)
      rw [he]
    · exfalso
      have : D.d * ℓ + D.d ≤ D.d * ℓ' := D.dmul_eq_of_le (by omega)
      omega
  · rintro ⟨ℓ', hl1', hl2', hval⟩
    rcases hu with ⟨ℓ, h1a, h2a, rfl⟩ | ⟨ℓ, h1a, h2a, rfl⟩
    · exact ⟨ℓ, h1a, h2a, rfl⟩
    · exfalso
      have : D.d * ℓ' + D.d ≤ D.d * ℓ := D.dmul_eq_of_le (by omega)
      omega

/-- An expansion step of the first free gadget. -/
lemma D₁_step {p u u' : ℤ} (hp2 : p ≤ D.pz)
    (hu : u ∈ D.D₁ (p - 1)) (hu' : u' ∈ D.D₁ p) (h1 : -1 ≤ u' - u) (h2 : u' - u ≤ D.d - 1) :
    (D.isA u → u' = u) ∧ (D.isA u' → D.isA u) := by
  have ht := D.one_le_tz
  have hdp := D.d_pos
  have hpt := D.pz_le_tz
  have hdt := D.d_big
  obtain ⟨hq0, hq1, hu⟩ := hu
  obtain ⟨hr0, hr1, hu'⟩ := hu'
  constructor
  · rintro ⟨ℓ, hl1, hl2, rfl⟩
    rcases hu' with ⟨ℓ', h1', h2', rfl⟩ | ⟨ℓ', h1', h2', rfl⟩
    · have e1 : D.d * ℓ' + 0 = D.d * ℓ + (D.d * ℓ' - D.d * ℓ) := by ring
      obtain ⟨he, -⟩ := D.slot_unique e1 (by omega) (by omega)
      rw [he]
    · exfalso
      have : D.d * ℓ + D.d ≤ D.d * ℓ' := D.dmul_eq_of_le (by omega)
      omega
  · rintro ⟨ℓ', hl1', hl2', hval⟩
    rcases hu with ⟨ℓ, h1a, h2a, rfl⟩ | ⟨ℓ, h1a, h2a, rfl⟩
    · exact ⟨ℓ, h1a, h2a, rfl⟩
    · exfalso
      have : D.d * ℓ' + D.d ≤ D.d * ℓ := D.dmul_eq_of_le (by omega)
      omega

/-- A compression step of the second free gadget: now the `B` indices do not move. -/
lemma C₂_step {p u u' : ℤ} (hp1 : 1 ≤ p)
    (hu : u ∈ D.C₂ (p - 1)) (hu' : u' ∈ D.C₂ p) (h1 : -1 ≤ u' - u) (h2 : u' - u ≤ D.d - 1) :
    (D.isB u → u' = u) ∧ (D.isB u' → D.isB u) := by
  have ht := D.one_le_tz
  have hdp := D.d_pos
  have hpt := D.pz_le_tz
  have hdt := D.d_big
  obtain ⟨-, -, hu⟩ := hu
  obtain ⟨-, -, hu'⟩ := hu'
  constructor
  · rintro ⟨ℓ, hl1, hl2, rfl⟩
    rcases hu' with ⟨ℓ', h1', h2', rfl⟩ | ⟨ℓ', h1', h2', rfl⟩
    · have e1 : D.d * ℓ' + 0 = D.d * ℓ + (D.d * ℓ' - D.d * ℓ) := by ring
      obtain ⟨he, -⟩ := D.slot_unique e1 (by omega) (by omega)
      rw [he]
    · exfalso
      have : D.d * ℓ' + D.d ≤ D.d * ℓ := D.dmul_eq_of_le (by omega)
      omega
  · rintro ⟨ℓ', hl1', hl2', hval⟩
    rcases hu with ⟨ℓ, h1a, h2a, rfl⟩ | ⟨ℓ, h1a, h2a, rfl⟩
    · exact ⟨ℓ, h1a, h2a, rfl⟩
    · exfalso
      have : D.d * ℓ + D.d ≤ D.d * ℓ' := D.dmul_eq_of_le (by omega)
      omega

/-- An expansion step of the second free gadget. -/
lemma D₂_step {p u u' : ℤ} (hp2 : p ≤ D.pz)
    (hu : u ∈ D.D₂ (p - 1)) (hu' : u' ∈ D.D₂ p) (h1 : -D.d + 1 ≤ u' - u) (h2 : u' - u ≤ 1) :
    (D.isB u → u' = u) ∧ (D.isB u' → D.isB u) := by
  have ht := D.one_le_tz
  have hdp := D.d_pos
  have hpt := D.pz_le_tz
  have hdt := D.d_big
  obtain ⟨hq0, hq1, hu⟩ := hu
  obtain ⟨hr0, hr1, hu'⟩ := hu'
  constructor
  · rintro ⟨ℓ, hl1, hl2, rfl⟩
    rcases hu' with ⟨ℓ', h1', h2', rfl⟩ | ⟨ℓ', h1', h2', rfl⟩
    · have e1 : D.d * ℓ' + 0 = D.d * ℓ + (D.d * ℓ' - D.d * ℓ) := by ring
      obtain ⟨he, -⟩ := D.slot_unique e1 (by omega) (by omega)
      rw [he]
    · exfalso
      have : D.d * ℓ' + D.d ≤ D.d * ℓ := D.dmul_eq_of_le (by omega)
      omega
  · rintro ⟨ℓ', hl1', hl2', hval⟩
    rcases hu with ⟨ℓ, h1a, h2a, rfl⟩ | ⟨ℓ, h1a, h2a, rfl⟩
    · exact ⟨ℓ, h1a, h2a, rfl⟩
    · exfalso
      have : D.d * ℓ + D.d ≤ D.d * ℓ' := D.dmul_eq_of_le (by omega)
      omega

end ABData

end ABSim

end StickPolyhex
