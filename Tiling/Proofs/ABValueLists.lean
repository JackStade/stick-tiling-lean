import Tiling.Proofs.ABSpecData

/-!
# The sets of values of the construction, as lists

Each of the sets of values used by the buckets of Sections 2.6–2.8 (`ABData.Efull`,
`ABData.Eset`, `ABData.Aset`, `ABData.Rload`, `ABData.Rreset`, `ABData.C₁`, `ABData.D₁`,
`ABData.C₂` and `ABData.D₂`) is a finite set of numbers between `1` and `v` given by an explicit
formula.  This file writes each of them as an explicit list of natural numbers and proves that
the list lists the set, in the sense of `ABSim.ListsSet`.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB

variable (S : ABTileSet) (hA : S.A ≠ [])

/-! ## The parameters of `abData` -/

@[simp] lemma abData_t : (abData S hA).t = tN S := rfl
@[simp] lemma abData_K : (abData S hA).K = kN S := rfl
@[simp] lemma abData_P : (abData S hA).P = pN S := rfl
@[simp] lemma abData_dN : (abData S hA).dN = dN S := rfl
@[simp] lemma abData_vN : (abData S hA).vN = vN S := rfl
@[simp] lemma abData_sN : (abData S hA).sN = sN S := rfl
@[simp] lemma abData_d : (abData S hA).d = (dN S : ℤ) := rfl
@[simp] lemma abData_kz : (abData S hA).kz = (kN S : ℤ) := rfl
@[simp] lemma abData_tz2 : (abData S hA).tz = (tN S : ℤ) := rfl
@[simp] lemma abData_pz : (abData S hA).pz = (pN S : ℤ) := rfl
@[simp] lemma abData_vz : (abData S hA).vz = (vN S : ℤ) := rfl

include hA in
lemma one_le_tN' : 1 ≤ tN S := (one_le_tN S).2 (Or.inl hA)

/-! ## Bounds -/

include hA in
lemma pN_le_tN : pN S ≤ tN S := by
  have := one_le_tN' S hA
  simp only [pN]
  omega

lemma one_le_pN : 1 ≤ pN S := by simp only [pN]; omega

lemma dN_le_mul {l : ℕ} (h : 1 ≤ l) : dN S ≤ dN S * l := Nat.le_mul_of_pos_right _ (by omega)

lemma mul_le_two_t {l : ℕ} (h : l ≤ 2 * tN S) : dN S * l ≤ dN S * (2 * tN S) :=
  Nat.mul_le_mul_left _ h

include hA in
lemma bound_add {l o : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ 2 * tN S) (ho : o ≤ 6 * kN S + tN S) :
    1 ≤ dN S * l + o ∧ dN S * l + o ≤ vN S := by
  have hk := one_le_kN S
  have ht := one_le_tN' S hA
  have hd1 := dN_le_mul S h1
  have hd2 := mul_le_two_t S h2
  have hdk := twelve_kN_le_dN S
  have hdt := twelve_tN_le_dN S
  have hv := vN_eq S
  omega

include hA in
lemma bound_sub {l o : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ 2 * tN S) (ho : o ≤ 6 * kN S + tN S) :
    1 ≤ dN S * l - o ∧ dN S * l - o ≤ vN S := by
  have hk := one_le_kN S
  have ht := one_le_tN' S hA
  have hd1 := dN_le_mul S h1
  have hd2 := mul_le_two_t S h2
  have hdk := twelve_kN_le_dN S
  have hdt := twelve_tN_le_dN S
  have hv := vN_eq S
  omega

/-! ## The colors are smaller than the number of colors -/

lemma tileAN_lt (l : ℕ) :
    (tileAN S l).ul < kN S ∧ (tileAN S l).ur < kN S ∧ (tileAN S l).ll < kN S ∧
      (tileAN S l).lr < kN S := by
  have := getD_color_le S.A (S.A ++ S.B) ((l - 1) % S.A.length)
    (fun u hu => List.mem_append_left _ hu)
  simp only [kN, kcount, tileAN]
  omega

lemma tileBN_lt (l : ℕ) :
    (tileBN S l).ul < kN S ∧ (tileBN S l).ur < kN S ∧ (tileBN S l).ll < kN S ∧
      (tileBN S l).lr < kN S := by
  have := getD_color_le S.B (S.A ++ S.B) ((l - 1 - tcount S) % S.B.length)
    (fun u hu => List.mem_append_right _ hu)
  simp only [kN, kcount, tileBN]
  omega

lemma hcolorN_lt {f g : ABTile → ℕ}
    (hf : ∀ u : ABTile, f u = u.ul ∨ f u = u.ur ∨ f u = u.ll ∨ f u = u.lr)
    (hg : ∀ u : ABTile, g u = u.ul ∨ g u = u.ur ∨ g u = u.ll ∨ g u = u.lr) (l : ℕ) :
    hcolorN S f g l < kN S := by
  simp only [hcolorN]
  split
  · have h1 := tileAN_lt S l
    rcases hf (tileAN S l) with h | h | h | h <;> rw [h] <;> omega
  · have h1 := tileBN_lt S l
    rcases hg (tileBN S l) with h | h | h | h <;> rw [h] <;> omega

lemma g₁N_lt (l : ℕ) : g₁N S l ≤ 5 * kN S - 1 := by
  have := hcolorN_lt S (fun _ => Or.inr (Or.inl rfl)) (fun _ => Or.inr (Or.inr (Or.inl rfl))) l
  simp only [g₁N]
  split <;> omega

lemma g₂N_lt (l : ℕ) : g₂N S l ≤ 5 * kN S - 1 := by
  have := hcolorN_lt S (fun _ => Or.inl rfl) (fun _ => Or.inr (Or.inr (Or.inr rfl))) l
  simp only [g₂N]
  split <;> omega

lemma g₃N_lt (l : ℕ) : g₃N S l ≤ 5 * kN S - 1 := by
  have := hcolorN_lt S (fun _ => Or.inr (Or.inr (Or.inr rfl))) (fun _ => Or.inl rfl) l
  simp only [g₃N]
  split <;> omega

lemma g₄N_lt (l : ℕ) : g₄N S l ≤ 5 * kN S - 1 := by
  have := hcolorN_lt S (fun _ => Or.inr (Or.inr (Or.inl rfl))) (fun _ => Or.inr (Or.inl rfl)) l
  simp only [g₄N]
  split <;> omega

lemma g₁N_eq {l : ℕ} (hl : 1 ≤ l) : ((g₁N S l : ℕ) : ℤ) = (abData S hA).g₁ (l : ℤ) := by
  simp only [g₁N, ABData.g₁, abData_h₁, abData_kz, abData_tz2]
  have h := hcolorN_eq S (f := ABTile.ur) (g := ABTile.ll) hl
  by_cases hc : l ≤ tN S
  · rw [if_pos hc, if_pos (by exact_mod_cast hc)]
    push_cast [h]
    ring
  · rw [if_neg hc, if_neg (by exact_mod_cast hc)]
    push_cast [h]
    ring

lemma g₂N_eq {l : ℕ} (hl : 1 ≤ l) : ((g₂N S l : ℕ) : ℤ) = (abData S hA).g₂ (l : ℤ) := by
  simp only [g₂N, ABData.g₂, abData_h₂, abData_kz, abData_tz2]
  have h := hcolorN_eq S (f := ABTile.ul) (g := ABTile.lr) hl
  by_cases hc : l ≤ tN S
  · rw [if_pos hc, if_pos (by exact_mod_cast hc)]
    push_cast [h]
    ring
  · rw [if_neg hc, if_neg (by exact_mod_cast hc)]
    push_cast [h]
    ring

lemma g₃N_eq {l : ℕ} (hl : 1 ≤ l) : ((g₃N S l : ℕ) : ℤ) = (abData S hA).g₃ (l : ℤ) := by
  simp only [g₃N, ABData.g₃, abData_h₃, abData_kz, abData_tz2]
  have h := hcolorN_eq S (f := ABTile.lr) (g := ABTile.ul) hl
  by_cases hc : l ≤ tN S
  · rw [if_pos hc, if_pos (by exact_mod_cast hc)]
    push_cast [h]
    ring
  · rw [if_neg hc, if_neg (by exact_mod_cast hc)]
    push_cast [h]
    ring

lemma g₄N_eq {l : ℕ} (hl : 1 ≤ l) : ((g₄N S l : ℕ) : ℤ) = (abData S hA).g₄ (l : ℤ) := by
  simp only [g₄N, ABData.g₄, abData_h₄, abData_kz, abData_tz2]
  have h := hcolorN_eq S (f := ABTile.ll) (g := ABTile.ur) hl
  by_cases hc : l ≤ tN S
  · rw [if_pos hc, if_pos (by exact_mod_cast hc)]
    push_cast [h]
    ring
  · rw [if_neg hc, if_neg (by exact_mod_cast hc)]
    push_cast [h]
    ring

/-! ## The lists -/

/-- All the values `1, …, v`. -/
def EfullL : List ℕ := slotList 1 (vN S) id

/-- The encoding values `d ℓ`. -/
def EsetL : List ℕ := slotList 1 (2 * tN S) (fun l => dN S * l)

/-- The values allowed in the second bucket of a matching gadget. -/
def AsetL : List ℕ :=
  slotList 1 (2 * tN S) (fun l => dN S * l + 2 * kN S) ++
    slotList2 1 (2 * tN S) 0 (2 * kN S - 2) (fun l e => dN S * l + e - (3 * kN S - 1))

/-- The loaded values of a matching gadget with load function `gN`. -/
def RloadL (gN : ℕ → ℕ) : List ℕ := slotList 1 (2 * tN S) (fun l => dN S * l + gN l)

/-- All third-state offsets of the paper's matching gadget. -/
def RresetL : List ℕ :=
  slotList2 1 (2 * tN S) 0 (6 * kN S - 1) (fun l x => dN S * l + x)

/-- The `p`-th set of the compression half of the first free gadget. -/
def C₁L (p : ℕ) : List ℕ :=
  if p ≤ pN S then
    slotList 1 (tN S) (fun l => dN S * l) ++
      slotList (tN S + 1) (max (tN S + 1) (2 * tN S - p)) (fun l => dN S * l + p)
  else []

/-- The `p`-th set of the expansion half of the first free gadget. -/
def D₁L (p : ℕ) : List ℕ :=
  if p ≤ pN S then
    slotList 1 (tN S) (fun l => dN S * l) ++
      slotList (tN S + 1) (min (2 * tN S) (tN S + 1 + p)) (fun l => dN S * l + (pN S - p))
  else []

/-- The `p`-th set of the compression half of the second free gadget. -/
def C₂L (p : ℕ) : List ℕ :=
  if p ≤ pN S then
    slotList (tN S + 1) (2 * tN S) (fun l => dN S * l) ++
      slotList (min (tN S) (1 + p)) (tN S) (fun l => dN S * l - p)
  else []

/-- The `p`-th set of the expansion half of the second free gadget. -/
def D₂L (p : ℕ) : List ℕ :=
  if p ≤ pN S then
    slotList (tN S + 1) (2 * tN S) (fun l => dN S * l) ++
      slotList (max 1 (tN S - p)) (tN S) (fun l => dN S * l - (pN S - p))
  else []

/-! ## The lists list the sets -/

include hA in
lemma listsSet_EfullL : ListsSet (vN S) (EfullL S) (abData S hA).Efull := by
  refine listsSet_slot (F := fun l => l) ?_ ?_ ?_
  · intro u
    simp only [ABData.Efull, abData_vz, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨u, by exact_mod_cast h1, by exact_mod_cast h2, rfl⟩
    · rintro ⟨l, h1, h2, rfl⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · intro l _ _
    simp
  · intro l h1 h2
    exact ⟨h1, h2⟩

include hA in
lemma listsSet_EsetL : ListsSet (vN S) (EsetL S) (abData S hA).Eset := by
  refine listsSet_slot (F := fun l => (dN S : ℤ) * l) ?_ ?_ ?_
  · intro u
    simp only [ABData.Eset, abData_d, abData_tz2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨l, h1, h2, rfl⟩
      exact ⟨l, by exact_mod_cast h1, by push_cast; exact_mod_cast h2, rfl⟩
    · rintro ⟨l, h1, h2, rfl⟩
      exact ⟨l, by exact_mod_cast h1, by push_cast at h2 ⊢; exact_mod_cast h2, rfl⟩
  · intro l _ _
    push_cast
    ring
  · intro l h1 h2
    have := bound_add S hA (l := l) (o := 0) h1 h2 (by omega)
    omega

include hA in
lemma listsSet_AsetL : ListsSet (vN S) (AsetL S) (abData S hA).Aset := by
  have hk := one_le_kN S
  have ht := one_le_tN' S hA
  have hdk := twelve_kN_le_dN S
  refine listsSet_congr (X := {u : ℤ | ∃ j : ℤ, 1 ≤ j ∧ j ≤ 2 * (tN S : ℤ) ∧
      u = (dN S : ℤ) * j + 2 * (kN S : ℤ)} ∪
    {u : ℤ | ∃ j : ℤ, 1 ≤ j ∧ j ≤ 2 * (tN S : ℤ) ∧ ∃ e : ℤ, (0 : ℤ) ≤ e ∧
      e ≤ ((2 * kN S - 2 : ℕ) : ℤ) ∧
      u = (dN S : ℤ) * j + e - ((3 * kN S - 1 : ℕ) : ℤ)}) (listsSet_append ?_ ?_) ?_
  · refine listsSet_slot (F := fun j => (dN S : ℤ) * j + 2 * (kN S : ℤ)) ?_ ?_ ?_
    · intro u
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, h1, h2, rfl⟩
        exact ⟨j, by exact_mod_cast h1, by push_cast; exact_mod_cast h2, rfl⟩
      · rintro ⟨j, h1, h2, rfl⟩
        exact ⟨j, by exact_mod_cast h1, by push_cast at h2 ⊢; exact_mod_cast h2, rfl⟩
    · intro l _ _
      push_cast
      ring
    · intro l h1 h2
      exact bound_add S hA h1 h2 (by omega)
  · refine listsSet_slot2 (F := fun j e => (dN S : ℤ) * j + e - ((3 * kN S - 1 : ℕ) : ℤ)) ?_ ?_ ?_
    · intro u
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, h1, h2, e, he1, he2, rfl⟩
        exact ⟨j, by exact_mod_cast h1, by push_cast; exact_mod_cast h2, e,
          by exact_mod_cast he1, by exact_mod_cast he2, rfl⟩
      · rintro ⟨j, h1, h2, e, he1, he2, rfl⟩
        exact ⟨j, by exact_mod_cast h1, by push_cast at h2 ⊢; exact_mod_cast h2, e,
          by exact_mod_cast he1, by exact_mod_cast he2, rfl⟩
    · intro l e h1 h2 _ he2
      have hd1 := dN_le_mul S h1
      have : ((dN S * l + e - (3 * kN S - 1) : ℕ) : ℤ)
          = ((dN S * l + e : ℕ) : ℤ) - ((3 * kN S - 1 : ℕ) : ℤ) := by omega
      rw [this]
      push_cast
      ring
    · intro l e h1 h2 _ he2
      have hd1 := dN_le_mul S h1
      have hb := bound_add S hA (l := l) (o := e) h1 h2 (by omega)
      omega
  · ext u
    simp only [ABData.Aset, abData_d, abData_tz2, abData_kz, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro (⟨j, h1, h2, rfl⟩ | ⟨j, h1, h2, e, he1, he2, rfl⟩)
      · exact ⟨j, h1, h2, Or.inl rfl⟩
      · refine ⟨j, h1, h2, Or.inr ⟨e - (kN S : ℤ) + 1, by omega, by omega, ?_⟩⟩
        have h3 : ((3 * kN S - 1 : ℕ) : ℤ) = 3 * (kN S : ℤ) - 1 := by omega
        rw [h3]
        ring
    · rintro ⟨j, h1, h2, (rfl | ⟨e, he1, he2, rfl⟩)⟩
      · exact Or.inl ⟨j, h1, h2, rfl⟩
      · refine Or.inr ⟨j, h1, h2, e + (kN S : ℤ) - 1, by omega, by omega, ?_⟩
        have h3 : ((3 * kN S - 1 : ℕ) : ℤ) = 3 * (kN S : ℤ) - 1 := by omega
        rw [h3]
        ring

include hA in
lemma listsSet_RloadL {gN : ℕ → ℕ} {g : ℤ → ℤ}
    (hcast : ∀ l : ℕ, 1 ≤ l → ((gN l : ℕ) : ℤ) = g (l : ℤ))
    (hb : ∀ l : ℕ, gN l ≤ 5 * kN S - 1) :
    ListsSet (vN S) (RloadL S gN) ((abData S hA).Rload g) := by
  have hk := one_le_kN S
  refine listsSet_slot (F := fun l => (dN S : ℤ) * l + g l) ?_ ?_ ?_
  · intro u
    simp only [ABData.Rload, abData_d, abData_tz2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨l, h1, h2, rfl⟩
      exact ⟨l, by exact_mod_cast h1, by push_cast; exact_mod_cast h2, rfl⟩
    · rintro ⟨l, h1, h2, rfl⟩
      exact ⟨l, by exact_mod_cast h1, by push_cast at h2 ⊢; exact_mod_cast h2, rfl⟩
  · intro l h1 _
    push_cast [hcast l h1]
    ring
  · intro l h1 h2
    have := hb l
    exact bound_add S hA h1 h2 (by omega)

include hA in
lemma listsSet_RresetL : ListsSet (vN S) (RresetL S) (abData S hA).Rreset := by
  have hk := one_le_kN S
  have ht := one_le_tN' S hA
  have h6 : ((6 * kN S - 1 : ℕ) : ℤ) = 6 * (kN S : ℤ) - 1 := by omega
  refine listsSet_slot2 (F := fun l x => (dN S : ℤ) * l + x) ?_ ?_ ?_
  · intro u
    simp only [ABData.Rreset, abData_d, abData_tz2, abData_kz, Set.mem_setOf_eq,
      Nat.cast_mul, Nat.cast_ofNat, h6]
    constructor <;> rintro ⟨l, h1, h2, x, hx0, hx6, rfl⟩ <;>
      exact ⟨l, h1, h2, x, hx0, by omega, rfl⟩
  · intro l x h1 h2 hx0 hx6
    push_cast
    ring
  · intro l x h1 h2 hx0 hx6
    exact bound_add S hA h1 h2 (by omega)


include hA in
lemma listsSet_C₁L (p : ℕ) : ListsSet (vN S) (C₁L S p) ((abData S hA).C₁ (p : ℤ)) := by
  have ht := one_le_tN' S hA
  have hpt := pN_le_tN S hA
  have hk := one_le_kN S
  have hdt := twelve_tN_le_dN S
  by_cases hp : p ≤ pN S
  · rw [C₁L, if_pos hp]
    refine listsSet_congr (X := {u : ℤ | ∃ l : ℤ, ((1 : ℕ) : ℤ) ≤ l ∧ l ≤ ((tN S : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l} ∪ {u : ℤ | ∃ l : ℤ, ((tN S + 1 : ℕ) : ℤ) ≤ l ∧ l ≤ ((max (tN S + 1) (2 * tN S - p) : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l + ((p : ℕ) : ℤ)}) (listsSet_append ?_ ?_) ?_
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l) (fun u => by simp) ?_ ?_
      · intro l _ _
        push_cast
        ring
      · intro l h1 h2
        exact bound_add S hA (o := 0) (by omega) (by omega) (by omega)
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l + ((p : ℕ) : ℤ)) (fun u => by simp) ?_ ?_
      · intro l h1 h2
        push_cast
        ring
      · intro l h1 h2
        exact bound_add S hA (o := p) (by omega) (by omega) (by omega)
    · ext u
      simp only [ABData.C₁, abData_d, abData_tz2, abData_pz, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inl ⟨l, by omega, by omega, rfl⟩⟩
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inr ⟨l, by omega, by omega, rfl⟩⟩
      · rintro ⟨-, -, (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)⟩
        · exact Or.inl ⟨l, by omega, by omega, rfl⟩
        · exact Or.inr ⟨l, by omega, by omega, rfl⟩
  · rw [C₁L, if_neg hp]
    refine listsSet_nil ?_
    rintro x ⟨-, h1, -⟩
    simp only [abData_pz] at h1
    exact hp (by exact_mod_cast h1)

include hA in
lemma listsSet_D₁L (p : ℕ) : ListsSet (vN S) (D₁L S p) ((abData S hA).D₁ (p : ℤ)) := by
  have ht := one_le_tN' S hA
  have hpt := pN_le_tN S hA
  have hk := one_le_kN S
  have hdt := twelve_tN_le_dN S
  by_cases hp : p ≤ pN S
  · rw [D₁L, if_pos hp]
    refine listsSet_congr (X := {u : ℤ | ∃ l : ℤ, ((1 : ℕ) : ℤ) ≤ l ∧ l ≤ ((tN S : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l} ∪ {u : ℤ | ∃ l : ℤ, ((tN S + 1 : ℕ) : ℤ) ≤ l ∧ l ≤ ((min (2 * tN S) (tN S + 1 + p) : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l + ((pN S : ℤ) - (p : ℤ))}) (listsSet_append ?_ ?_) ?_
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l) (fun u => by simp) ?_ ?_
      · intro l _ _
        push_cast
        ring
      · intro l h1 h2
        exact bound_add S hA (o := 0) (by omega) (by omega) (by omega)
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l + ((pN S : ℤ) - (p : ℤ))) (fun u => by simp) ?_ ?_
      · intro l h1 h2
        have hcast : ((pN S - p : ℕ) : ℤ) = (pN S : ℤ) - (p : ℤ) := by omega
        push_cast [hcast]
        ring
      · intro l h1 h2
        exact bound_add S hA (o := pN S - p) (by omega) (by omega) (by omega)
    · ext u
      simp only [ABData.D₁, abData_d, abData_tz2, abData_pz, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inl ⟨l, by omega, by omega, rfl⟩⟩
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inr ⟨l, by omega, by omega, rfl⟩⟩
      · rintro ⟨-, -, (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)⟩
        · exact Or.inl ⟨l, by omega, by omega, rfl⟩
        · exact Or.inr ⟨l, by omega, by omega, rfl⟩
  · rw [D₁L, if_neg hp]
    refine listsSet_nil ?_
    rintro x ⟨-, h1, -⟩
    simp only [abData_pz] at h1
    exact hp (by exact_mod_cast h1)

include hA in
lemma listsSet_C₂L (p : ℕ) : ListsSet (vN S) (C₂L S p) ((abData S hA).C₂ (p : ℤ)) := by
  have ht := one_le_tN' S hA
  have hpt := pN_le_tN S hA
  have hk := one_le_kN S
  have hdt := twelve_tN_le_dN S
  by_cases hp : p ≤ pN S
  · rw [C₂L, if_pos hp]
    refine listsSet_congr (X := {u : ℤ | ∃ l : ℤ, ((tN S + 1 : ℕ) : ℤ) ≤ l ∧ l ≤ ((2 * tN S : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l} ∪ {u : ℤ | ∃ l : ℤ, ((min (tN S) (1 + p) : ℕ) : ℤ) ≤ l ∧ l ≤ ((tN S : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l - ((p : ℕ) : ℤ)}) (listsSet_append ?_ ?_) ?_
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l) (fun u => by simp) ?_ ?_
      · intro l _ _
        push_cast
        ring
      · intro l h1 h2
        exact bound_add S hA (o := 0) (by omega) (by omega) (by omega)
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l - ((p : ℕ) : ℤ)) (fun u => by simp) ?_ ?_
      · intro l h1 h2
        have hd1 := dN_le_mul S (show 1 ≤ l by omega)
        have hcast : ((dN S * l - p : ℕ) : ℤ) = ((dN S * l : ℕ) : ℤ) - (p : ℤ) := by omega
        rw [hcast]
        push_cast
        ring
      · intro l h1 h2
        exact bound_sub S hA (o := p) (by omega) (by omega) (by omega)
    · ext u
      simp only [ABData.C₂, abData_d, abData_tz2, abData_pz, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inl ⟨l, by omega, by omega, rfl⟩⟩
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inr ⟨l, by omega, by omega, rfl⟩⟩
      · rintro ⟨-, -, (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)⟩
        · exact Or.inl ⟨l, by omega, by omega, rfl⟩
        · exact Or.inr ⟨l, by omega, by omega, rfl⟩
  · rw [C₂L, if_neg hp]
    refine listsSet_nil ?_
    rintro x ⟨-, h1, -⟩
    simp only [abData_pz] at h1
    exact hp (by exact_mod_cast h1)

include hA in
lemma listsSet_D₂L (p : ℕ) : ListsSet (vN S) (D₂L S p) ((abData S hA).D₂ (p : ℤ)) := by
  have ht := one_le_tN' S hA
  have hpt := pN_le_tN S hA
  have hk := one_le_kN S
  have hdt := twelve_tN_le_dN S
  by_cases hp : p ≤ pN S
  · rw [D₂L, if_pos hp]
    refine listsSet_congr (X := {u : ℤ | ∃ l : ℤ, ((tN S + 1 : ℕ) : ℤ) ≤ l ∧ l ≤ ((2 * tN S : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l} ∪ {u : ℤ | ∃ l : ℤ, ((max 1 (tN S - p) : ℕ) : ℤ) ≤ l ∧ l ≤ ((tN S : ℕ) : ℤ) ∧ u = (dN S : ℤ) * l - ((pN S : ℤ) - (p : ℤ))}) (listsSet_append ?_ ?_) ?_
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l) (fun u => by simp) ?_ ?_
      · intro l _ _
        push_cast
        ring
      · intro l h1 h2
        exact bound_add S hA (o := 0) (by omega) (by omega) (by omega)
    · refine listsSet_slot (F := fun l => (dN S : ℤ) * l - ((pN S : ℤ) - (p : ℤ))) (fun u => by simp) ?_ ?_
      · intro l h1 h2
        have hd1 := dN_le_mul S (show 1 ≤ l by omega)
        have hcast : ((dN S * l - (pN S - p) : ℕ) : ℤ) = ((dN S * l : ℕ) : ℤ) - ((pN S : ℤ) - (p : ℤ)) := by omega
        rw [hcast]
        push_cast
        ring
      · intro l h1 h2
        exact bound_sub S hA (o := pN S - p) (by omega) (by omega) (by omega)
    · ext u
      simp only [ABData.D₂, abData_d, abData_tz2, abData_pz, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inl ⟨l, by omega, by omega, rfl⟩⟩
        · exact ⟨by positivity, by exact_mod_cast hp, Or.inr ⟨l, by omega, by omega, rfl⟩⟩
      · rintro ⟨-, -, (⟨l, h1, h2, rfl⟩ | ⟨l, h1, h2, rfl⟩)⟩
        · exact Or.inl ⟨l, by omega, by omega, rfl⟩
        · exact Or.inr ⟨l, by omega, by omega, rfl⟩
  · rw [D₂L, if_neg hp]
    refine listsSet_nil ?_
    rintro x ⟨-, h1, -⟩
    simp only [abData_pz] at h1
    exact hp (by exact_mod_cast h1)

end ABSim

end StickPolyhex
