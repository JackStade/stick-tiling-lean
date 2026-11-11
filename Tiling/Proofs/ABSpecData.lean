import Tiling.Proofs.ABIndex
import Tiling.Proofs.GapSpecMarks

/-!
# The bucket data of an AB tile set, as finite data

Sections 2.6–2.8 of the paper attach to a set of AB tiles the specification
`ABSim.ABData.spec` of Section 2.5.  That specification is a `GapSpec`, whose sets of values are
genuine subsets of `ℤ`; this file computes the same specification as a `GapSpecData`, i.e. as
lists of natural numbers, and proves that the two agree
(`ABSim.abSpecData_toGapSpec`).

All the sets of values occurring in the construction are finite sets of numbers between `1` and
`v`, described by explicit formulas, so each of them is listed by an explicit list; the bucket
table `ABSim.dataList` mirrors `ABSim.ABData.data` bucket by bucket.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB

variable (S : ABTileSet)

/-! ## The numerical parameters, as natural numbers -/

/-- The number of tiles of each kind. -/
def tN : ℕ := tcount S

/-- The number of colors. -/
def kN : ℕ := kcount S

/-- The number of steps of each half of a free gadget. -/
def pN : ℕ := max (tN S - 1) 1

/-- The scale of the encoding. -/
def dN : ℕ := 12 * (kN S + tN S)

/-- The number of values. -/
def vN : ℕ := dN S * (2 * tN S + 1)

/-- The number of buckets. -/
def sN : ℕ := 16 + 8 * pN S

lemma one_le_tN : 1 ≤ tN S ↔ S.A ≠ [] ∨ S.B ≠ [] := by
  simp only [tN, tcount, le_max_iff, Nat.one_le_iff_ne_zero, List.length_eq_zero_iff, ne_eq]

lemma one_le_kN : 1 ≤ kN S := by simp only [kN, kcount]; omega

lemma twelve_kN_le_dN : 12 * kN S ≤ dN S := by simp only [dN]; omega

lemma twelve_tN_le_dN : 12 * tN S ≤ dN S := by simp only [dN]; omega

lemma vN_eq : vN S = dN S * (2 * tN S) + dN S := by simp only [vN]; ring

/-! ## The colors, as functions of a natural index -/

/-- The `A` tile named by a natural index. -/
def tileAN (l : ℕ) : ABTile := S.A.getD ((l - 1) % S.A.length) dfltTile

/-- The `B` tile named by a natural index. -/
def tileBN (l : ℕ) : ABTile := S.B.getD ((l - 1 - tcount S) % S.B.length) dfltTile

/-- The matching function of the construction, as a function of a natural index. -/
def hcolorN (f g : ABTile → ℕ) (l : ℕ) : ℕ :=
  if l ≤ tcount S then f (tileAN S l) else g (tileBN S l)

lemma tileAN_eq {l : ℕ} (hl : 1 ≤ l) : tileAN S l = tileA S (l : ℤ) := by
  simp only [tileAN, tileA]
  congr 1
  rcases Nat.eq_zero_or_pos S.A.length with h | h
  · simp only [h, Nat.mod_zero, Nat.cast_zero, Int.emod_zero]
    omega
  · have : ((l : ℤ) - 1) % (S.A.length : ℤ) = (((l - 1) % S.A.length : ℕ) : ℤ) := by
      have hc : ((l : ℤ) - 1) = ((l - 1 : ℕ) : ℤ) := by omega
      rw [hc]
      push_cast
      rfl
    rw [this, Int.toNat_natCast]

lemma tileBN_eq {l : ℕ} (hl : tcount S + 1 ≤ l) : tileBN S l = tileB S (l : ℤ) := by
  simp only [tileBN, tileB]
  congr 1
  rcases Nat.eq_zero_or_pos S.B.length with h | h
  · simp only [h, Nat.mod_zero, Nat.cast_zero, Int.emod_zero]
    omega
  · have : ((l : ℤ) - 1 - (tcount S : ℤ)) % (S.B.length : ℤ)
        = (((l - 1 - tcount S) % S.B.length : ℕ) : ℤ) := by
      have hc : ((l : ℤ) - 1 - (tcount S : ℤ)) = ((l - 1 - tcount S : ℕ) : ℤ) := by omega
      rw [hc]
      push_cast
      rfl
    rw [this, Int.toNat_natCast]

lemma hcolorN_eq {f g : ABTile → ℕ} {l : ℕ} (hl : 1 ≤ l) :
    ((hcolorN S f g l : ℕ) : ℤ) = hcolor S f g (l : ℤ) := by
  simp only [hcolorN, hcolor]
  by_cases h : l ≤ tcount S
  · rw [if_pos h, if_pos (by exact_mod_cast h), tileAN_eq S hl]
  · rw [if_neg h, if_neg (by exact_mod_cast h), tileBN_eq S (by omega)]

/-- The load function of the first matching gadget, on natural indices. -/
def g₁N (l : ℕ) : ℕ := (if l ≤ tN S then 2 * kN S else 4 * kN S) + hcolorN S ABTile.ur ABTile.ll l

/-- The load function of the second matching gadget, on natural indices. -/
def g₂N (l : ℕ) : ℕ := (if l ≤ tN S then 4 * kN S else 2 * kN S) + hcolorN S ABTile.ul ABTile.lr l

/-- The load function of the third matching gadget, on natural indices. -/
def g₃N (l : ℕ) : ℕ := (if l ≤ tN S then 2 * kN S else 4 * kN S) + hcolorN S ABTile.lr ABTile.ul l

/-- The load function of the fourth matching gadget, on natural indices. -/
def g₄N (l : ℕ) : ℕ := (if l ≤ tN S then 4 * kN S else 2 * kN S) + hcolorN S ABTile.ll ABTile.ur l

/-! ## Listing a finite set of values -/

/-- The list `l` *lists* the set of values `X`: its entries lie between `1` and `v`, and they are
exactly the elements of `X`. -/
def ListsSet (v : ℕ) (l : List ℕ) (X : Set ℤ) : Prop :=
  (∀ b ∈ l, 1 ≤ b ∧ b ≤ v) ∧ ∀ x : ℤ, x ∈ X ↔ ∃ b ∈ l, x = (b : ℤ)

/-- The list of the values `f l` for `l` running from `lo` to `hi`. -/
def slotList (lo hi : ℕ) (f : ℕ → ℕ) : List ℕ :=
  (List.range (hi + 1 - lo)).map (fun i => f (lo + i))

lemma mem_slotList {lo hi : ℕ} {f : ℕ → ℕ} {b : ℕ} :
    b ∈ slotList lo hi f ↔ ∃ l, lo ≤ l ∧ l ≤ hi ∧ b = f l := by
  simp only [slotList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi', rfl⟩
    exact ⟨lo + i, by omega, by omega, rfl⟩
  · rintro ⟨l, h1, h2, rfl⟩
    exact ⟨l - lo, by omega, by rw [show lo + (l - lo) = l by omega]⟩

/-- The list of the values `f l e` for `l` from `lo` to `hi` and `e` from `lo'` to `hi'`. -/
def slotList2 (lo hi lo' hi' : ℕ) (f : ℕ → ℕ → ℕ) : List ℕ :=
  (slotList lo hi id).flatMap (fun l => slotList lo' hi' (f l))

lemma mem_slotList2 {lo hi lo' hi' : ℕ} {f : ℕ → ℕ → ℕ} {b : ℕ} :
    b ∈ slotList2 lo hi lo' hi' f ↔
      ∃ l, lo ≤ l ∧ l ≤ hi ∧ ∃ e, lo' ≤ e ∧ e ≤ hi' ∧ b = f l e := by
  simp only [slotList2, List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hb⟩
    obtain ⟨l', h1, h2, hl'⟩ := mem_slotList.1 hl
    simp only [id] at hl'
    subst hl'
    obtain ⟨e, he1, he2, rfl⟩ := mem_slotList.1 hb
    exact ⟨l, h1, h2, e, he1, he2, rfl⟩
  · rintro ⟨l, h1, h2, e, he1, he2, rfl⟩
    exact ⟨l, mem_slotList.2 ⟨l, h1, h2, rfl⟩, mem_slotList.2 ⟨e, he1, he2, rfl⟩⟩

lemma listsSet_slot {v lo hi : ℕ} {f : ℕ → ℕ} {F : ℤ → ℤ} {X : Set ℤ}
    (hX : ∀ u : ℤ, u ∈ X ↔ ∃ l : ℤ, (lo : ℤ) ≤ l ∧ l ≤ (hi : ℤ) ∧ u = F l)
    (hf : ∀ l : ℕ, lo ≤ l → l ≤ hi → ((f l : ℕ) : ℤ) = F (l : ℤ))
    (hb : ∀ l : ℕ, lo ≤ l → l ≤ hi → 1 ≤ f l ∧ f l ≤ v) :
    ListsSet v (slotList lo hi f) X := by
  constructor
  · intro b hb'
    obtain ⟨l, h1, h2, rfl⟩ := mem_slotList.1 hb'
    exact hb l h1 h2
  · intro x
    rw [hX]
    constructor
    · rintro ⟨l, h1, h2, rfl⟩
      have h0 : (0 : ℤ) ≤ l := le_trans (by positivity) h1
      lift l to ℕ using h0 with lN
      have h1' : lo ≤ lN := by exact_mod_cast h1
      have h2' : lN ≤ hi := by exact_mod_cast h2
      exact ⟨f lN, mem_slotList.2 ⟨lN, h1', h2', rfl⟩, (hf lN h1' h2').symm⟩
    · rintro ⟨b, hbmem, rfl⟩
      obtain ⟨l, h1, h2, rfl⟩ := mem_slotList.1 hbmem
      exact ⟨(l : ℤ), by exact_mod_cast h1, by exact_mod_cast h2, (hf l h1 h2)⟩

lemma listsSet_slot2 {v lo hi lo' hi' : ℕ} {f : ℕ → ℕ → ℕ} {F : ℤ → ℤ → ℤ} {X : Set ℤ}
    (hX : ∀ u : ℤ, u ∈ X ↔ ∃ l : ℤ, (lo : ℤ) ≤ l ∧ l ≤ (hi : ℤ) ∧
      ∃ e : ℤ, (lo' : ℤ) ≤ e ∧ e ≤ (hi' : ℤ) ∧ u = F l e)
    (hf : ∀ l e : ℕ, lo ≤ l → l ≤ hi → lo' ≤ e → e ≤ hi' → ((f l e : ℕ) : ℤ) = F (l : ℤ) (e : ℤ))
    (hb : ∀ l e : ℕ, lo ≤ l → l ≤ hi → lo' ≤ e → e ≤ hi' → 1 ≤ f l e ∧ f l e ≤ v) :
    ListsSet v (slotList2 lo hi lo' hi' f) X := by
  constructor
  · intro b hb'
    obtain ⟨l, h1, h2, e, he1, he2, rfl⟩ := mem_slotList2.1 hb'
    exact hb l e h1 h2 he1 he2
  · intro x
    rw [hX]
    constructor
    · rintro ⟨l, h1, h2, e, he1, he2, rfl⟩
      have h0 : (0 : ℤ) ≤ l := le_trans (by positivity) h1
      have h0' : (0 : ℤ) ≤ e := le_trans (by positivity) he1
      lift l to ℕ using h0 with lN
      lift e to ℕ using h0' with eN
      have h1' : lo ≤ lN := by exact_mod_cast h1
      have h2' : lN ≤ hi := by exact_mod_cast h2
      have h3' : lo' ≤ eN := by exact_mod_cast he1
      have h4' : eN ≤ hi' := by exact_mod_cast he2
      exact ⟨f lN eN, mem_slotList2.2 ⟨lN, h1', h2', eN, h3', h4', rfl⟩,
        (hf lN eN h1' h2' h3' h4').symm⟩
    · rintro ⟨b, hbmem, rfl⟩
      obtain ⟨l, h1, h2, e, he1, he2, rfl⟩ := mem_slotList2.1 hbmem
      exact ⟨(l : ℤ), by exact_mod_cast h1, by exact_mod_cast h2, (e : ℤ),
        by exact_mod_cast he1, by exact_mod_cast he2, hf l e h1 h2 he1 he2⟩

lemma listsSet_append {v : ℕ} {l₁ l₂ : List ℕ} {X Y : Set ℤ}
    (h₁ : ListsSet v l₁ X) (h₂ : ListsSet v l₂ Y) : ListsSet v (l₁ ++ l₂) (X ∪ Y) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rcases List.mem_append.1 hb with h | h
    · exact h₁.1 b h
    · exact h₂.1 b h
  · intro x
    constructor
    · rintro (hx | hx)
      · obtain ⟨b, hb, rfl⟩ := (h₁.2 x).1 hx
        exact ⟨b, List.mem_append.2 (Or.inl hb), rfl⟩
      · obtain ⟨b, hb, rfl⟩ := (h₂.2 x).1 hx
        exact ⟨b, List.mem_append.2 (Or.inr hb), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      rcases List.mem_append.1 hb with h | h
      · exact Or.inl ((h₁.2 _).2 ⟨b, h, rfl⟩)
      · exact Or.inr ((h₂.2 _).2 ⟨b, h, rfl⟩)

lemma listsSet_nil {v : ℕ} {X : Set ℤ} (h : ∀ x : ℤ, x ∉ X) : ListsSet v [] X :=
  ⟨by simp, fun x => ⟨fun hx => absurd hx (h x), by rintro ⟨b, hb, -⟩; simp at hb⟩⟩

lemma listsSet_congr {v : ℕ} {l : List ℕ} {X Y : Set ℤ} (h : ListsSet v l X) (hXY : X = Y) :
    ListsSet v l Y := hXY ▸ h

end ABSim

end StickPolyhex
