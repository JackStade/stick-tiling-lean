import Tiling.Proofs.LineAssignment

/-!
# The buckets simulating a set of AB tiles (Sections 2.6–2.8 of the paper)

Given a set of AB tiles, Sections 2.6–2.8 of the paper construct the data of Section 2.5 — the
number `s` of buckets, the number `v` of values and, for every bucket `i`, the sets `L i`, `R i`
of allowed left and right values and the interval `I i` — in such a way that the gap conditions
can be satisfied exactly when the AB tiles tile the plane.  This file carries out the
construction; `Tiling/Proofs/ABForward.lean` and `Tiling/Proofs/ABBackward.lean` prove the two
implications and `Tiling/Proofs/ABMain.lean` states the equivalence.

## The data extracted from the AB tiles

Everything the construction needs from the tile set is packaged in `ABData`: the number `t` of
tiles of each of the two kinds, the number `K` of colors, and four *matching functions*
`h₁, h₂, h₃, h₄` on the indices `1, …, 2t` of the tiles (the index `ℓ ≤ t` denotes the `ℓ`-th `A`
tile and the index `ℓ > t` the `(ℓ - t)`-th `B` tile).  Each `hᵢ` reads one color of the tile,
chosen so that the four color-matching conditions of an AB tiling become the four equations
`hᵢ (index of one column) = hᵢ (index of the next column)`; see `Tiling/Proofs/ABIndex.lean`.

## The buckets

The matching table is the one from Section 2.8, with load bases `2K` and `4K`,
intervals `[0, 6K]`, and all offsets in `[0, 6K)` permitted in the third state.
We retain the larger scale `d = 12 (K + t)` for uniform bounds, and the free-gadget
padding `P = max (t-1) 1` for the singleton case.

The values are the numbers `1, …, v` with `v = d (2t+1)`, where `d = 12 (K + t)`; a tile index
`ℓ` is encoded by the value `d ℓ`.  The `s = 16 + 8P` buckets (`P = max (t-1) 1`) are grouped
into six gadgets, each gadget acting on the values of one row of gaps as the rows sweep downwards:

* four *matching gadgets* of four buckets each.  A matching gadget for a function `h` leaves the
  encoded index of every gap unchanged, and forces the indices of two adjacent gaps to be of
  opposite kinds (`A` next to `B`) and to carry the same color `h` across every boundary from an
  `A` index to a `B` index (or, for the mirrored variant, across every boundary from a `B` index
  to an `A` index).
* two *free gadgets* of `4P` buckets each.  A free gadget leaves every `A` index unchanged and
  lets every `B` index change arbitrarily (or the other way round for the mirrored variant); it
  does so by pushing the `B` indices, one step at a time, into a single slot and then letting
  them spread out again, which is why it needs `Θ(t)` buckets.

The bucket data is assembled in `ABData.data`, a function from the bucket index to the triple
(set of left values, set of right values, interval), and `ABData.spec` packages it as a
`GapSpec`.
-/

namespace StickPolyhex

namespace ABSim

/-- The data extracted from a set of AB tiles: the number `t` of tiles of each kind, the number
`K` of colors, and the four matching functions on tile indices `1, …, 2t`.  The function `h₁`
reads the upper-right color of an `A` tile and the lower-left color of a `B` tile, `h₂` the
upper-left color of an `A` tile and the lower-right color of a `B` tile, `h₃` the lower-right
color of an `A` tile and the upper-left color of a `B` tile, and `h₄` the lower-left color of an
`A` tile and the upper-right color of a `B` tile. -/
structure ABData where
  /-- The number of tiles of each of the two kinds. -/
  t : ℕ
  /-- The number of colors. -/
  K : ℕ
  /-- There is at least one tile of each kind. -/
  ht : 1 ≤ t
  /-- There is at least one color. -/
  hK : 1 ≤ K
  /-- The matching function checked across a boundary from an `A` column to a `B` column in the
  first of the two bands of a cycle. -/
  h₁ : ℤ → ℤ
  /-- The matching function checked across a boundary from a `B` column to an `A` column in the
  first of the two bands of a cycle. -/
  h₂ : ℤ → ℤ
  /-- The matching function checked across a boundary from an `A` column to a `B` column in the
  second of the two bands of a cycle. -/
  h₃ : ℤ → ℤ
  /-- The matching function checked across a boundary from a `B` column to an `A` column in the
  second of the two bands of a cycle. -/
  h₄ : ℤ → ℤ
  /-- The matching functions take values among the `K` colors. -/
  h₁_mem : ∀ ℓ, 0 ≤ h₁ ℓ ∧ h₁ ℓ < (K : ℤ)
  /-- The matching functions take values among the `K` colors. -/
  h₂_mem : ∀ ℓ, 0 ≤ h₂ ℓ ∧ h₂ ℓ < (K : ℤ)
  /-- The matching functions take values among the `K` colors. -/
  h₃_mem : ∀ ℓ, 0 ≤ h₃ ℓ ∧ h₃ ℓ < (K : ℤ)
  /-- The matching functions take values among the `K` colors. -/
  h₄_mem : ∀ ℓ, 0 ≤ h₄ ℓ ∧ h₄ ℓ < (K : ℤ)

namespace ABData

variable (D : ABData)

/-! ### The numerical parameters -/

/-- The number of steps of each half of a free gadget. -/
def P : ℕ := max (D.t - 1) 1

/-- The scale of the encoding: a tile index `ℓ` is encoded by the value `d * ℓ`. -/
def dN : ℕ := 12 * (D.K + D.t)

/-- The number of values. -/
def vN : ℕ := D.dN * (2 * D.t + 1)

/-- The number of buckets. -/
def sN : ℕ := 16 + 8 * D.P

/-- The scale, as an integer. -/
def d : ℤ := (D.dN : ℤ)

/-- The number of tiles of each kind, as an integer. -/
def tz : ℤ := (D.t : ℤ)

/-- The number of colors, as an integer. -/
def kz : ℤ := (D.K : ℤ)

/-- The number of steps of each half of a free gadget, as an integer. -/
def pz : ℤ := (D.P : ℤ)

/-- The number of values, as an integer. -/
def vz : ℤ := (D.vN : ℤ)

lemma one_le_tz : 1 ≤ D.tz := by
  have := D.ht; unfold tz; exact_mod_cast this

lemma one_le_kz : 1 ≤ D.kz := by
  have := D.hK; unfold kz; exact_mod_cast this

lemma pz_le_tz : D.pz ≤ D.tz := by
  have := D.ht
  have : D.P ≤ D.t := by unfold P; omega
  unfold pz tz; exact_mod_cast this

lemma one_le_pz : 1 ≤ D.pz := by
  have : 1 ≤ D.P := by unfold P; omega
  unfold pz; exact_mod_cast this

lemma tz_le_pz_add_one : D.tz ≤ D.pz + 1 := by
  have := D.ht
  have h : D.t ≤ D.P + 1 := by unfold P; omega
  unfold pz tz; exact_mod_cast h

lemma h₁_lt (ℓ : ℤ) : 0 ≤ D.h₁ ℓ ∧ D.h₁ ℓ < D.kz := D.h₁_mem ℓ

lemma h₂_lt (ℓ : ℤ) : 0 ≤ D.h₂ ℓ ∧ D.h₂ ℓ < D.kz := D.h₂_mem ℓ

lemma h₃_lt (ℓ : ℤ) : 0 ≤ D.h₃ ℓ ∧ D.h₃ ℓ < D.kz := D.h₃_mem ℓ

lemma h₄_lt (ℓ : ℤ) : 0 ≤ D.h₄ ℓ ∧ D.h₄ ℓ < D.kz := D.h₄_mem ℓ

lemma d_eq : D.d = 12 * (D.kz + D.tz) := by
  unfold d dN kz tz; push_cast; ring

lemma vz_eq : D.vz = D.d * (2 * D.tz + 1) := by
  unfold vz vN d tz; push_cast; ring

lemma d_pos : 0 < D.d := by
  have := D.one_le_kz; have := D.one_le_tz; rw [D.d_eq]; omega

lemma d_big : 12 * D.kz ≤ D.d ∧ 12 * D.tz ≤ D.d := by
  have := D.one_le_kz; have := D.one_le_tz; rw [D.d_eq]; omega

/-! ### Multiplication toolkit -/

lemma dle {m n : ℤ} (h : D.d * m ≤ D.d * n) : m ≤ n :=
  le_of_mul_le_mul_left h D.d_pos

lemma dlt {m n : ℤ} (h : D.d * m < D.d * n) : m < n :=
  lt_of_mul_lt_mul_left h (le_of_lt D.d_pos)

/-- The basic separation fact: a value determines its slot and its offset, as soon as the
difference of the offsets is smaller than the scale. -/
lemma slot_unique {ℓ ℓ' o o' : ℤ} (h : D.d * ℓ + o = D.d * ℓ' + o')
    (h1 : -D.d < o - o') (h2 : o - o' < D.d) : ℓ = ℓ' ∧ o = o' := by
  have key : ℓ = ℓ' := by
    rcases lt_trichotomy ℓ ℓ' with hlt | heq | hgt
    · exfalso
      have : D.d * (ℓ + 1) ≤ D.d * ℓ' := by
        apply mul_le_mul_of_nonneg_left (by omega) (le_of_lt D.d_pos)
      have hd : D.d * ℓ + D.d ≤ D.d * ℓ' := by linarith [this, mul_add D.d ℓ 1]
      omega
    · exact heq
    · exfalso
      have : D.d * (ℓ' + 1) ≤ D.d * ℓ := by
        apply mul_le_mul_of_nonneg_left (by omega) (le_of_lt D.d_pos)
      have hd : D.d * ℓ' + D.d ≤ D.d * ℓ := by linarith [this, mul_add D.d ℓ' 1]
      omega
  subst key
  exact ⟨rfl, by omega⟩

/-- A bound on `d * m` below the scale forces `m ≤ 0`. -/
lemma slot_le_zero {m c : ℤ} (h : D.d * m ≤ c) (hc : c < D.d) : m ≤ 0 := by
  have : D.d * m < D.d * 1 := by rw [mul_one]; omega
  have := D.dlt this
  omega

/-- A bound on `d * m` above minus twice the scale forces `-1 ≤ m`. -/
lemma slot_neg_one_le {m c : ℤ} (h : c ≤ D.d * m) (hc : -2 * D.d < c) : -1 ≤ m := by
  by_contra hm
  have hm2 : m ≤ -2 := by omega
  have h1 : D.d * m ≤ D.d * (-2) :=
    mul_le_mul_of_nonneg_left hm2 (le_of_lt D.d_pos)
  have h2 : D.d * (-2) = -2 * D.d := by ring
  omega

/-- The values used by the construction all lie in the range `1, …, v`. -/
lemma mem_range_of_slot {ℓ o : ℤ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz)
    (ho : -(6 * D.kz + D.tz) ≤ o) (ho' : o ≤ 6 * D.kz + D.tz) :
    1 ≤ D.d * ℓ + o ∧ D.d * ℓ + o ≤ D.vz := by
  have hd := D.d_big
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  constructor
  · have : D.d * 1 ≤ D.d * ℓ := mul_le_mul_of_nonneg_left h1 (le_of_lt D.d_pos)
    rw [mul_one] at this
    omega
  · have : D.d * ℓ ≤ D.d * (2 * D.tz) := mul_le_mul_of_nonneg_left h2 (le_of_lt D.d_pos)
    rw [D.vz_eq]
    nlinarith [D.d_pos]

/-! ### The load functions of the four matching gadgets -/

/-- The load function of a matching gadget: the value `d ℓ` of a gap is moved by `g ℓ`, which
records both the kind of the tile (through the base `2K` or `4K`) and one of its colors. -/
def g₁ (ℓ : ℤ) : ℤ := (if ℓ ≤ D.tz then 2 * D.kz else 4 * D.kz) + D.h₁ ℓ

/-- The load function of the second matching gadget; the two bases are exchanged, so that the
color is checked across the boundaries from a `B` index to an `A` index. -/
def g₂ (ℓ : ℤ) : ℤ := (if ℓ ≤ D.tz then 4 * D.kz else 2 * D.kz) + D.h₂ ℓ

/-- The load function of the third matching gadget. -/
def g₃ (ℓ : ℤ) : ℤ := (if ℓ ≤ D.tz then 2 * D.kz else 4 * D.kz) + D.h₃ ℓ

/-- The load function of the fourth matching gadget. -/
def g₄ (ℓ : ℤ) : ℤ := (if ℓ ≤ D.tz then 4 * D.kz else 2 * D.kz) + D.h₄ ℓ

lemma g₁_bounds (ℓ : ℤ) : 2 * D.kz ≤ D.g₁ ℓ ∧ D.g₁ ℓ ≤ 5 * D.kz - 1 := by
  have := D.h₁_lt ℓ; unfold g₁; split <;> omega

lemma g₂_bounds (ℓ : ℤ) : 2 * D.kz ≤ D.g₂ ℓ ∧ D.g₂ ℓ ≤ 5 * D.kz - 1 := by
  have := D.h₂_lt ℓ; unfold g₂; split <;> omega

lemma g₃_bounds (ℓ : ℤ) : 2 * D.kz ≤ D.g₃ ℓ ∧ D.g₃ ℓ ≤ 5 * D.kz - 1 := by
  have := D.h₃_lt ℓ; unfold g₃; split <;> omega

lemma g₄_bounds (ℓ : ℤ) : 2 * D.kz ≤ D.g₄ ℓ ∧ D.g₄ ℓ ≤ 5 * D.kz - 1 := by
  have := D.h₄_lt ℓ; unfold g₄; split <;> omega

/-! ### The sets of values -/

/-- All the values: `1, …, v`. -/
def Efull : Set ℤ := Set.Icc 1 D.vz

/-- The encoding set: the values `d ℓ` of the tile indices `ℓ = 1, …, 2t`. -/
def Eset : Set ℤ := {u | ∃ ℓ : ℤ, 1 ≤ ℓ ∧ ℓ ≤ 2 * D.tz ∧ u = D.d * ℓ}

/-- The set of right values allowed in the second bucket of a matching gadget.  It permits the
offset `2K` (with no color difference) and any offset `-2K + e` with `|e| < K`; this is what
forces the kinds of two adjacent indices to alternate and the colors to agree. -/
def Aset : Set ℤ := {u | ∃ j : ℤ, 1 ≤ j ∧ j ≤ 2 * D.tz ∧
  (u = D.d * j + 2 * D.kz ∨ ∃ e : ℤ, -D.kz < e ∧ e < D.kz ∧ u = D.d * j - 2 * D.kz + e)}

/-- The set of loaded values `d ℓ + g ℓ` of a matching gadget. -/
def Rload (g : ℤ → ℤ) : Set ℤ := {u | ∃ ℓ : ℤ, 1 ≤ ℓ ∧ ℓ ≤ 2 * D.tz ∧ u = D.d * ℓ + g ℓ}

/-- The third-state values of the paper's matching gadget: an arbitrary nonnegative
offset smaller than `6K` above an encoding slot. -/
def Rreset : Set ℤ := {u | ∃ ℓ : ℤ, 1 ≤ ℓ ∧ ℓ ≤ 2 * D.tz ∧
  ∃ x : ℤ, 0 ≤ x ∧ x < 6 * D.kz ∧ u = D.d * ℓ + x}

/-- The `p`-th set of the compression half of the first free gadget: the `A` indices stay on the
grid, while the `B` indices have been pushed `p` steps down and carry the offset `p`. -/
def C₁ (p : ℤ) : Set ℤ := {u | 0 ≤ p ∧ p ≤ D.pz ∧
  ((∃ ℓ : ℤ, 1 ≤ ℓ ∧ ℓ ≤ D.tz ∧ u = D.d * ℓ) ∨
   (∃ ℓ : ℤ, D.tz + 1 ≤ ℓ ∧ ℓ ≤ max (D.tz + 1) (2 * D.tz - p) ∧ u = D.d * ℓ + p))}

/-- The `p`-th set of the expansion half of the first free gadget. -/
def D₁ (p : ℤ) : Set ℤ := {u | 0 ≤ p ∧ p ≤ D.pz ∧
  ((∃ ℓ : ℤ, 1 ≤ ℓ ∧ ℓ ≤ D.tz ∧ u = D.d * ℓ) ∨
   (∃ ℓ : ℤ, D.tz + 1 ≤ ℓ ∧ ℓ ≤ min (2 * D.tz) (D.tz + 1 + p) ∧ u = D.d * ℓ + (D.pz - p)))}

/-- The `p`-th set of the compression half of the second free gadget: now the `B` indices stay on
the grid and the `A` indices are pushed `p` steps up, carrying the offset `-p`. -/
def C₂ (p : ℤ) : Set ℤ := {u | 0 ≤ p ∧ p ≤ D.pz ∧
  ((∃ ℓ : ℤ, D.tz + 1 ≤ ℓ ∧ ℓ ≤ 2 * D.tz ∧ u = D.d * ℓ) ∨
   (∃ ℓ : ℤ, min D.tz (1 + p) ≤ ℓ ∧ ℓ ≤ D.tz ∧ u = D.d * ℓ - p))}

/-- The `p`-th set of the expansion half of the second free gadget. -/
def D₂ (p : ℤ) : Set ℤ := {u | 0 ≤ p ∧ p ≤ D.pz ∧
  ((∃ ℓ : ℤ, D.tz + 1 ≤ ℓ ∧ ℓ ≤ 2 * D.tz ∧ u = D.d * ℓ) ∨
   (∃ ℓ : ℤ, max 1 (D.tz - p) ≤ ℓ ∧ ℓ ≤ D.tz ∧ u = D.d * ℓ - (D.pz - p)))}

/-! ### The sets are sets of values -/

lemma Efull_subset : D.Efull ⊆ Set.Icc 1 D.vz := le_refl _

lemma Eset_subset : D.Eset ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨ℓ, h1, h2, rfl⟩
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hr := D.mem_range_of_slot (ℓ := ℓ) (o := 0) h1 h2 (by omega) (by omega)
  constructor <;> omega

lemma Aset_subset : D.Aset ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨j, h1, h2, h⟩
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  rcases h with rfl | ⟨e, he1, he2, rfl⟩
  · exact Set.mem_Icc.2 (D.mem_range_of_slot h1 h2 (by omega) (by omega))
  · have := D.mem_range_of_slot (ℓ := j) (o := -2 * D.kz + e) h1 h2 (by omega) (by omega)
    constructor <;> [omega; omega]

lemma Rload_subset {g : ℤ → ℤ} (hg : ∀ ℓ, 2 * D.kz ≤ g ℓ ∧ g ℓ ≤ 5 * D.kz - 1) :
    D.Rload g ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨ℓ, h1, h2, rfl⟩
  have := hg ℓ
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  exact Set.mem_Icc.2 (D.mem_range_of_slot h1 h2 (by omega) (by omega))

lemma Rreset_subset : D.Rreset ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨ℓ, h1, h2, x, hx0, hx6, rfl⟩
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  exact Set.mem_Icc.2 (D.mem_range_of_slot h1 h2 (by omega) (by omega))

lemma C₁_subset (p : ℤ) : D.C₁ p ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨hp0, hp1, h⟩
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  rcases h with ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩
  · have hr := D.mem_range_of_slot (ℓ := ℓ) (o := 0) (by omega) (by omega) (by omega) (by omega)
    constructor <;> omega
  · have hmax : ℓ ≤ 2 * D.tz := le_trans h2 (by omega)
    exact Set.mem_Icc.2 (D.mem_range_of_slot (by omega) hmax (by omega) (by omega))

lemma D₁_subset (p : ℤ) : D.D₁ p ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨hp0, hp1, h⟩
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  rcases h with ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩
  · have hr := D.mem_range_of_slot (ℓ := ℓ) (o := 0) (by omega) (by omega) (by omega) (by omega)
    constructor <;> omega
  · have hmax : ℓ ≤ 2 * D.tz := le_trans h2 (by omega)
    exact Set.mem_Icc.2 (D.mem_range_of_slot (by omega) hmax (by omega) (by omega))

lemma C₂_subset (p : ℤ) : D.C₂ p ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨hp0, hp1, h⟩
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  rcases h with ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩
  · have hr := D.mem_range_of_slot (ℓ := ℓ) (o := 0) (by omega) (by omega) (by omega) (by omega)
    constructor <;> omega
  · have hmin : 1 ≤ ℓ := le_trans (by omega) h1
    have := D.mem_range_of_slot (ℓ := ℓ) (o := -p) hmin (by omega) (by omega) (by omega)
    constructor <;> [omega; omega]

lemma D₂_subset (p : ℤ) : D.D₂ p ⊆ Set.Icc 1 D.vz := by
  rintro u ⟨hp0, hp1, h⟩
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hpt := D.pz_le_tz
  rcases h with ⟨ℓ, h1, h2, rfl⟩ | ⟨ℓ, h1, h2, rfl⟩
  · have hr := D.mem_range_of_slot (ℓ := ℓ) (o := 0) (by omega) (by omega) (by omega) (by omega)
    constructor <;> omega
  · have hmin : 1 ≤ ℓ := le_trans (by omega) h1
    have := D.mem_range_of_slot (ℓ := ℓ) (o := -(D.pz - p)) hmin (by omega) (by omega) (by omega)
    constructor <;> [omega; omega]

end ABData

/-! ## The bucket table -/

/-- The data attached to a single bucket: the set of allowed left values, the set of allowed
right values, and the two ends of the interval. -/
structure StateSpec where
  /-- The allowed left values. -/
  L : Set ℤ
  /-- The allowed right values. -/
  R : Set ℤ
  /-- The left end of the interval. -/
  lo : ℤ
  /-- The right end of the interval. -/
  hi : ℤ

namespace ABData

variable (D : ABData)

/-- The four buckets of a matching gadget with load function `g`, indexed by `i = 1, 2, 3, 4`. -/
def matchData (g : ℤ → ℤ) (i : ℕ) : StateSpec :=
  if i = 1 then ⟨D.Efull, D.Rload g, 0, 6 * D.kz⟩
  else if i = 2 then ⟨D.Eset, D.Aset, 0, 6 * D.kz⟩
  else if i = 3 then ⟨D.Efull, D.Rreset, 0, 6 * D.kz⟩
  else ⟨D.Eset, D.Eset, 0, 6 * D.kz⟩

/-- The `4P` buckets of the first free gadget (the `A` indices are locked, the `B` indices are
free), indexed by `i = 1, …, 4P`. -/
def freeData₁ (i : ℕ) : StateSpec :=
  if i ≤ 2 * D.P then
    (if i % 2 = 1 then ⟨D.Efull, D.C₁ (((i + 1) / 2 : ℕ) : ℤ), -D.d + 1, 1⟩
     else ⟨D.C₁ (((i / 2 : ℕ)) : ℤ), D.Efull, 0, 0⟩)
  else
    (if (i - 2 * D.P) % 2 = 1 then
        ⟨D.Efull, D.D₁ ((((i - 2 * D.P) + 1) / 2 : ℕ) : ℤ), -1, D.d - 1⟩
     else ⟨D.D₁ (((i - 2 * D.P) / 2 : ℕ) : ℤ),
            (if i = 4 * D.P then D.Eset else D.Efull), 0, 0⟩)

/-- The buckets of the second free gadget (the `B` indices are locked, the `A` indices are free),
indexed by `i = 1, …, 4P`; the last one is the bucket `1` of the table below. -/
def freeData₂ (i : ℕ) : StateSpec :=
  if i ≤ 2 * D.P then
    (if i % 2 = 1 then ⟨D.Efull, D.C₂ (((i + 1) / 2 : ℕ) : ℤ), -1, D.d - 1⟩
     else ⟨D.C₂ (((i / 2 : ℕ)) : ℤ), D.Efull, 0, 0⟩)
  else
    (if (i - 2 * D.P) % 2 = 1 then
        ⟨D.Efull, D.D₂ ((((i - 2 * D.P) + 1) / 2 : ℕ) : ℤ), -D.d + 1, 1⟩
     else ⟨D.D₂ (((i - 2 * D.P) / 2 : ℕ) : ℤ), D.Efull, 0, 0⟩)

/-- The table of the `s` buckets.  The bucket `1` is an *encoding* bucket, where the value of
every gap encodes the index of a tile; it is followed by two matching gadgets (buckets `2` to
`9`), the first free gadget (buckets `10` to `9 + 4P`), two more matching gadgets (buckets
`10 + 4P` to `17 + 4P`) and the second free gadget (buckets `18 + 4P` to `s`, its last bucket
being the bucket `1` again). -/
def data (q : ℕ) : StateSpec :=
  if q = 1 then ⟨D.Eset, D.Eset, 0, 0⟩
  else if q ≤ 5 then D.matchData D.g₁ (q - 1)
  else if q ≤ 9 then D.matchData D.g₂ (q - 5)
  else if q ≤ 9 + 4 * D.P then D.freeData₁ (q - 9)
  else if q ≤ 13 + 4 * D.P then D.matchData D.g₃ (q - 9 - 4 * D.P)
  else if q ≤ 17 + 4 * D.P then D.matchData D.g₄ (q - 13 - 4 * D.P)
  else if q ≤ D.sN then D.freeData₂ (q - 17 - 4 * D.P)
  else ⟨∅, ∅, 0, 0⟩

/-! ### The table takes values in the admissible sets and intervals -/

lemma matchData_L_subset (g : ℤ → ℤ) (i : ℕ) : (D.matchData g i).L ⊆ Set.Icc 1 D.vz := by
  unfold matchData
  split_ifs  <;>
    first
      | exact D.Efull_subset
      | exact D.Eset_subset

lemma matchData_R_subset {g : ℤ → ℤ} (hg : ∀ ℓ, 2 * D.kz ≤ g ℓ ∧ g ℓ ≤ 5 * D.kz - 1) (i : ℕ) :
    (D.matchData g i).R ⊆ Set.Icc 1 D.vz := by
  unfold matchData
  split_ifs  <;>
    first
      | exact D.Rload_subset hg
      | exact D.Aset_subset
      | exact D.Rreset_subset
      | exact D.Eset_subset

lemma matchData_interval (g : ℤ → ℤ) (i : ℕ) :
    -D.vz + 1 ≤ (D.matchData g i).lo ∧ (D.matchData g i).lo ≤ (D.matchData g i).hi ∧
      (D.matchData g i).hi ≤ D.vz - 1 := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hd := D.d_big
  have hv : D.d * 3 ≤ D.vz := by
    rw [D.vz_eq]
    have : D.d * 3 ≤ D.d * (2 * D.tz + 1) := mul_le_mul_of_nonneg_left (by omega) (le_of_lt D.d_pos)
    omega
  unfold matchData
  split_ifs <;> simp only [] <;> omega

lemma freeData₁_L_subset (i : ℕ) : (D.freeData₁ i).L ⊆ Set.Icc 1 D.vz := by
  unfold freeData₁
  split_ifs  <;>
    first
      | exact D.Efull_subset
      | exact D.C₁_subset _
      | exact D.D₁_subset _

lemma freeData₁_R_subset (i : ℕ) : (D.freeData₁ i).R ⊆ Set.Icc 1 D.vz := by
  unfold freeData₁
  split_ifs  <;>
    first
      | exact D.Efull_subset
      | exact D.Eset_subset
      | exact D.C₁_subset _
      | exact D.D₁_subset _

lemma freeData₂_L_subset (i : ℕ) : (D.freeData₂ i).L ⊆ Set.Icc 1 D.vz := by
  unfold freeData₂
  split_ifs  <;>
    first
      | exact D.Efull_subset
      | exact D.C₂_subset _
      | exact D.D₂_subset _

lemma freeData₂_R_subset (i : ℕ) : (D.freeData₂ i).R ⊆ Set.Icc 1 D.vz := by
  unfold freeData₂
  split_ifs  <;>
    first
      | exact D.Efull_subset
      | exact D.Eset_subset
      | exact D.C₂_subset _
      | exact D.D₂_subset _

lemma free_interval (i : ℕ) :
    (-D.vz + 1 ≤ (D.freeData₁ i).lo ∧ (D.freeData₁ i).lo ≤ (D.freeData₁ i).hi ∧
      (D.freeData₁ i).hi ≤ D.vz - 1) ∧
    (-D.vz + 1 ≤ (D.freeData₂ i).lo ∧ (D.freeData₂ i).lo ≤ (D.freeData₂ i).hi ∧
      (D.freeData₂ i).hi ≤ D.vz - 1) := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hd := D.d_big
  have hv : D.d * 3 ≤ D.vz := by
    rw [D.vz_eq]
    have : D.d * 3 ≤ D.d * (2 * D.tz + 1) := mul_le_mul_of_nonneg_left (by omega) (le_of_lt D.d_pos)
    omega
  constructor <;> [unfold freeData₁; unfold freeData₂] <;> split_ifs <;> simp only [] <;> omega

lemma data_L_subset (q : ℕ) : (D.data q).L ⊆ Set.Icc 1 D.vz := by
  unfold data
  split_ifs
  · exact D.Eset_subset
  · exact D.matchData_L_subset _ _
  · exact D.matchData_L_subset _ _
  · exact D.freeData₁_L_subset _
  · exact D.matchData_L_subset _ _
  · exact D.matchData_L_subset _ _
  · exact D.freeData₂_L_subset _
  · exact Set.empty_subset _

lemma data_R_subset (q : ℕ) : (D.data q).R ⊆ Set.Icc 1 D.vz := by
  unfold data
  split_ifs
  · exact D.Eset_subset
  · exact D.matchData_R_subset D.g₁_bounds _
  · exact D.matchData_R_subset D.g₂_bounds _
  · exact D.freeData₁_R_subset _
  · exact D.matchData_R_subset D.g₃_bounds _
  · exact D.matchData_R_subset D.g₄_bounds _
  · exact D.freeData₂_R_subset _
  · exact Set.empty_subset _

lemma data_interval (q : ℕ) :
    -D.vz + 1 ≤ (D.data q).lo ∧ (D.data q).lo ≤ (D.data q).hi ∧ (D.data q).hi ≤ D.vz - 1 := by
  have hk := D.one_le_kz
  have ht := D.one_le_tz
  have hd := D.d_big
  have hv : D.d * 3 ≤ D.vz := by
    rw [D.vz_eq]
    have : D.d * 3 ≤ D.d * (2 * D.tz + 1) := mul_le_mul_of_nonneg_left (by omega) (le_of_lt D.d_pos)
    omega
  unfold data
  split_ifs
  · simp only []
    omega
  · exact D.matchData_interval _ _
  · exact D.matchData_interval _ _
  · exact (D.free_interval _).1
  · exact D.matchData_interval _ _
  · exact D.matchData_interval _ _
  · exact (D.free_interval _).2
  · simp only []
    omega

/-! ### The specification -/

/-- The data of Section 2.5 built from a set of AB tiles: `s = 16 + 8P` buckets, `v = d(2t+1)`
values, and the sets and intervals of the table `ABData.data`. -/
def spec : GapSpec where
  s := D.sN
  v := D.vN
  hs := by unfold sN; omega
  hv := by
    have h1 := D.ht
    have h2 := D.hK
    have hd : 0 < D.dN := by unfold dN; omega
    have : 0 < D.vN := by unfold vN; exact Nat.mul_pos hd (by omega)
    omega
  L := fun q => (D.data q).L
  R := fun q => (D.data q).R
  hL := fun q => D.data_L_subset q
  hR := fun q => D.data_R_subset q
  Imin := fun q => (D.data q).lo
  Imax := fun q => (D.data q).hi
  hImin := fun q => (D.data_interval q).1
  hImax := fun q => (D.data_interval q).2.2
  hI := fun q => (D.data_interval q).2.1

@[simp] lemma spec_s : D.spec.s = D.sN := rfl
@[simp] lemma spec_v : D.spec.v = D.vN := rfl
@[simp] lemma spec_L (q : ℕ) : D.spec.L q = (D.data q).L := rfl
@[simp] lemma spec_R (q : ℕ) : D.spec.R q = (D.data q).R := rfl
@[simp] lemma spec_Imin (q : ℕ) : D.spec.Imin q = (D.data q).lo := rfl
@[simp] lemma spec_Imax (q : ℕ) : D.spec.Imax q = (D.data q).hi := rfl

end ABData

end ABSim

end StickPolyhex
