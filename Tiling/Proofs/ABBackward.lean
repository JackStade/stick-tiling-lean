import Tiling.Proofs.ABGadgets
import Tiling.Proofs.ABCycle
import Tiling.Proofs.ABIndex

/-!
# From a gap assignment to an index tiling

This file proves the hard direction of Sections 2.6–2.8: a gap assignment for the buckets built
from a set of AB tiles gives back an index tiling, hence an AB tiling of the plane.

A line assignment is read along the *time* `m`, the number of rows below a fixed reference row
`r₀` whose state is the first bucket: `Backward.Xv A r₀ c m` is the value carried in the row at
time `m` by the line of the column `c` and `Backward.Yv A r₀ c m` the value carried by the line
of gaps between the columns `c` and `c + 1`.  The state of the row at time `m` is the bucket
`pha m + 1`, so the gadgets are met one after the other as `m` increases.

The proof then follows the gadgets: `Backward.match_gadget` shows that a matching gadget returns
every value to where it was and forces the indices of two adjacent columns to alternate and their
colors to agree, while `Backward.free1_comp`, `Backward.free1_exp`, `Backward.free2_comp` and
`Backward.free2_exp` show that a free gadget leaves the locked family of indices untouched.
-/

namespace StickPolyhex

namespace ABSim

namespace Backward

variable {D : ABData} (A : LineAssignment D.spec) (r₀ : ℤ)

/-- The value carried by the line of the column `c` at the time `m`. -/
def Xv (c m : ℤ) : ℤ := A.V (r₀ + 2 * c) (r₀ - m)

/-- The value carried by the line of gaps between the columns `c` and `c + 1` at the time `m`. -/
def Yv (c m : ℤ) : ℤ := A.V (r₀ + 2 * c + 1) (r₀ - m)

variable {A r₀}

/-- The state of the row at the time `m` is the bucket `pha m + 1`. -/
lemma st_eq (hr₀ : A.st r₀ = 1) (m : ℤ) : A.st (r₀ - m) = D.pha m + 1 := by
  have hs : D.spec.s = D.sN := rfl
  have hd := D.decomp m
  have hrow : r₀ - m = (r₀ - (D.pha m : ℤ)) - (D.spec.s : ℤ) * D.cyc m := by
    rw [hs]; omega
  rw [hrow, A.st_period_int]
  have := A.st_add r₀ (D.pha m)
  rw [hr₀] at this
  have hlt : D.pha m < D.sN := D.pha_lt m
  rw [this, hs, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ### The four conditions, read at a time -/

lemma memX_even (hr₀ : A.st r₀ = 1) {c m : ℤ} (hm : m % 2 = 0) :
    Xv A r₀ c m ∈ (D.data (D.pha m + 1)).L := by
  have h := A.memL (r₀ - m) (r₀ + 2 * c) (by omega)
  rw [st_eq hr₀ m] at h
  exact h

lemma memY_even (hr₀ : A.st r₀ = 1) {c m : ℤ} (hm : m % 2 = 0) :
    Yv A r₀ c m ∈ (D.data (D.pha m + 1)).R := by
  have h := A.memR (r₀ - m) (r₀ + 2 * c + 1) (by omega)
  rw [st_eq hr₀ m] at h
  exact h

lemma memX_odd (hr₀ : A.st r₀ = 1) {c m : ℤ} (hm : m % 2 = 1) :
    Xv A r₀ c m ∈ (D.data (D.pha m + 1)).R := by
  have h := A.memR (r₀ - m) (r₀ + 2 * c) (by omega)
  rw [st_eq hr₀ m] at h
  exact h

lemma memY_odd (hr₀ : A.st r₀ = 1) {c m : ℤ} (hm : m % 2 = 1) :
    Yv A r₀ c m ∈ (D.data (D.pha m + 1)).L := by
  have h := A.memL (r₀ - m) (r₀ + 2 * c + 1) (by omega)
  rw [st_eq hr₀ m] at h
  exact h

lemma pair_even {c m : ℤ} (hm : m % 2 = 0) :
    Yv A r₀ c (m + 1) - Yv A r₀ c m = -(Xv A r₀ c (m + 1) - Xv A r₀ c m) := by
  have h := A.pair (r₀ - m) (r₀ + 2 * c) (by omega)
  have he : r₀ - m - 1 = r₀ - (m + 1) := by ring
  rw [he] at h
  have he2 : r₀ + 2 * c + 1 = r₀ + 2 * c + 1 := rfl
  simp only [Xv, Yv]
  omega

lemma pair_odd {c m : ℤ} (hm : m % 2 = 1) :
    Xv A r₀ (c + 1) (m + 1) - Xv A r₀ (c + 1) m = -(Yv A r₀ c (m + 1) - Yv A r₀ c m) := by
  have h := A.pair (r₀ - m) (r₀ + 2 * c + 1) (by omega)
  have he : r₀ - m - 1 = r₀ - (m + 1) := by ring
  rw [he] at h
  have hJ : r₀ + 2 * c + 1 + 1 = r₀ + 2 * (c + 1) := by ring
  rw [hJ] at h
  simp only [Xv, Yv]
  omega

lemma intv_even (hr₀ : A.st r₀ = 1) {c m : ℤ} (hm : m % 2 = 0) :
    (D.data (D.pha (m + 1) + 1)).lo ≤ Xv A r₀ c (m + 1) - Xv A r₀ c m ∧
      Xv A r₀ c (m + 1) - Xv A r₀ c m ≤ (D.data (D.pha (m + 1) + 1)).hi := by
  have h := A.intv (r₀ - m) (r₀ + 2 * c) (by omega)
  have he : r₀ - m - 1 = r₀ - (m + 1) := by ring
  rw [he, st_eq hr₀ (m + 1)] at h
  exact h

lemma intv_odd (hr₀ : A.st r₀ = 1) {c m : ℤ} (hm : m % 2 = 1) :
    (D.data (D.pha (m + 1) + 1)).lo ≤ Yv A r₀ c (m + 1) - Yv A r₀ c m ∧
      Yv A r₀ c (m + 1) - Yv A r₀ c m ≤ (D.data (D.pha (m + 1) + 1)).hi := by
  have h := A.intv (r₀ - m) (r₀ + 2 * c + 1) (by omega)
  have he : r₀ - m - 1 = r₀ - (m + 1) := by ring
  rw [he, st_eq hr₀ (m + 1)] at h
  exact h

/-! ### Reading the index encoded by a value -/

/-- The index encoded by a value of the encoding set. -/
lemma eset_slot {D : ABData} {u : ℤ} (h : u ∈ D.Eset) :
    u = D.d * (u / D.d) ∧ 1 ≤ u / D.d ∧ u / D.d ≤ 2 * D.tz := by
  obtain ⟨ℓ, h1, h2, rfl⟩ := h
  have hd : D.d ≠ 0 := by have := D.d_pos; omega
  rw [Int.mul_ediv_cancel_left ℓ hd]
  exact ⟨rfl, h1, h2⟩

/-! ### A matching gadget -/

/-- The effect of a matching gadget, read backwards: every line returns to the value it had at
the beginning of the gadget, and the load function of the gadget takes, on the indices of two
adjacent columns, either exactly the difference `2K` or a difference of at most `-K-1`. -/
lemma match_gadget (hr₀ : A.st r₀ = 1) {g : ℤ → ℤ}
    (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1) {m : ℤ} (hm : m % 2 = 0)
    (hd1 : D.data (D.pha (m + 1) + 1) = D.matchData g 1)
    (hd2 : D.data (D.pha (m + 2) + 1) = D.matchData g 2)
    (hd3 : D.data (D.pha (m + 3) + 1) = D.matchData g 3)
    (hd4 : D.data (D.pha (m + 4) + 1) = D.matchData g 4)
    (hX : ∀ c, Xv A r₀ c m ∈ D.Eset) (hY : ∀ c, Yv A r₀ c m ∈ D.Eset) :
    (∀ c, Xv A r₀ c (m + 4) = Xv A r₀ c m) ∧
      (∀ c, g (Xv A r₀ (c + 1) m / D.d) - g (Xv A r₀ c m / D.d) = 2 * D.kz ∨
        g (Xv A r₀ (c + 1) m / D.d) - g (Xv A r₀ c m / D.d) ≤ -D.kz - 1) := by
  have hk := D.one_le_kz
  set ℓ : ℤ → ℤ := fun c => Xv A r₀ c m / D.d with hℓdef
  have hXℓ : ∀ c, Xv A r₀ c m = D.d * ℓ c := fun c => (eset_slot (hX c)).1
  have hℓ1 : ∀ c, 1 ≤ ℓ c := fun c => (eset_slot (hX c)).2.1
  have hℓ2 : ∀ c, ℓ c ≤ 2 * D.tz := fun c => (eset_slot (hX c)).2.2
  -- the first step: every line is loaded by `g`
  have step1 : ∀ c, Xv A r₀ c (m + 1) = D.d * ℓ c + g (ℓ c) := by
    intro c
    have hmem := memX_odd (c := c) (m := m + 1) hr₀ (by omega)
    rw [hd1] at hmem
    have hint := intv_even (c := c) (m := m) hr₀ hm
    rw [hd1] at hint
    refine D.load_forced hgb hmem ?_ ?_ <;> rw [← hXℓ c] <;>
      simp only [ABData.matchData_one] at hint <;> omega
  have stepY1 : ∀ c, Yv A r₀ c (m + 1) = Yv A r₀ c m - g (ℓ c) := by
    intro c
    have h := pair_even (A := A) (r₀ := r₀) (c := c) (m := m) hm
    rw [step1 c, hXℓ c] at h
    omega
  -- the second step: every line is unloaded again, which forces the loads to match
  have step2 : ∀ c, Xv A r₀ c (m + 2) = D.d * ℓ c ∧
      Yv A r₀ (c - 1) (m + 2) - Yv A r₀ (c - 1) (m + 1) = g (ℓ c) := by
    intro c
    have hc : c - 1 + 1 = c := by ring
    have hpair := pair_odd (A := A) (r₀ := r₀) (c := c - 1) (m := m + 1) (by omega)
    rw [hc] at hpair
    have hint := intv_odd (c := c - 1) (m := m + 1) hr₀ (by omega)
    rw [show m + 1 + 1 = m + 2 by ring, hd2] at hint
    simp only [ABData.matchData_two] at hint
    have hmem := memX_even (c := c) (m := m + 2) hr₀ (by omega)
    rw [hd2] at hmem
    have hval : Xv A r₀ c (m + 2) = D.d * ℓ c := by
      refine D.unload_forced hgb hmem ?_ ?_
      · rw [← step1 c]
        rw [show m + 1 + 1 = m + 2 by ring] at hpair
        omega
      · rw [← step1 c]
        rw [show m + 1 + 1 = m + 2 by ring] at hpair
        omega
    refine ⟨hval, ?_⟩
    rw [show m + 1 + 1 = m + 2 by ring] at hpair
    rw [hval, step1 c] at hpair
    omega
  have hX2 : ∀ c, Xv A r₀ c (m + 2) = D.d * ℓ c := fun c => (step2 c).1
  have hY2 : ∀ c, Yv A r₀ c (m + 2) = Yv A r₀ c m - g (ℓ c) + g (ℓ (c + 1)) := by
    intro c
    have h := (step2 (c + 1)).2
    rw [show c + 1 - 1 = c by ring, stepY1 c] at h
    omega
  -- the alternation condition
  have halt : ∀ c, g (ℓ (c + 1)) - g (ℓ c) = 2 * D.kz ∨ g (ℓ (c + 1)) - g (ℓ c) ≤ -D.kz - 1 := by
    intro c
    obtain ⟨hμ, hμ1, hμ2⟩ := eset_slot (hY c)
    have hmem := memY_even (c := c) (m := m + 2) hr₀ (by omega)
    rw [hd2] at hmem
    simp only [ABData.matchData_two] at hmem
    rw [hY2 c, hμ] at hmem
    have hb := hgb (ℓ c)
    have hb' := hgb (ℓ (c + 1))
    have hshape : D.d * (Yv A r₀ c m / D.d) - g (ℓ c) + g (ℓ (c + 1)) =
        D.d * (Yv A r₀ c m / D.d) + (g (ℓ (c + 1)) - g (ℓ c)) := by ring
    rw [hshape] at hmem
    exact D.Aset_offset hμ1 hμ2 (by omega) (by omega) hmem
  -- The last two intervals preserve the index without fixing the intermediate value.
  have step4 : ∀ c, Xv A r₀ c (m + 4) = D.d * ℓ c := by
    intro c
    have hi3 := intv_even (A := A) (r₀ := r₀) (c := c) (m := m + 2) hr₀ (by omega)
    rw [show m + 2 + 1 = m + 3 by ring, hd3] at hi3
    simp only [ABData.matchData_three] at hi3
    rw [hX2 c] at hi3
    have hc : c - 1 + 1 = c := by ring
    have hpair := pair_odd (A := A) (r₀ := r₀) (c := c - 1) (m := m + 3) (by omega)
    rw [hc, show m + 3 + 1 = m + 4 by ring] at hpair
    have hi4 := intv_odd (c := c - 1) (m := m + 3) hr₀ (by omega)
    rw [show m + 3 + 1 = m + 4 by ring, hd4] at hi4
    simp only [ABData.matchData_four] at hi4
    have hmem := memX_even (c := c) (m := m + 4) hr₀ (by omega)
    rw [hd4] at hmem
    exact D.reset_forced hmem hi3.1 hi3.2 (by omega) (by omega)

  exact ⟨fun c => by rw [step4 c, hXℓ c], halt⟩

/-! ### Half of a free gadget -/

/-- Half of a free gadget, read backwards: whatever the values do, the locked family of indices
is untouched and no value of the free family becomes a locked index.  The hypothesis `hstep` is
the one-step statement proved in `Tiling/Proofs/ABGadgets.lean` for each of the four halves, and
`hdata` says which buckets are met: the odd times carry the set `S p` and the interval
`[lo, hi]`, the even times carry the interval `[0,0]`. -/
lemma free_half (hr₀ : A.st r₀ = 1) {S : ℤ → Set ℤ} {isL : ℤ → Prop} {lo hi : ℤ} {k : ℕ} {m : ℤ}
    (hm : m % 2 = 0)
    (hstep : ∀ q : ℕ, 1 ≤ q → q ≤ k → ∀ u u', u ∈ S ((q : ℤ) - 1) → u' ∈ S (q : ℤ) →
      lo ≤ u' - u → u' - u ≤ hi → (isL u → u' = u) ∧ (isL u' → isL u))
    (hdata : ∀ q : ℕ, q < k →
      (D.data (D.pha (m + 2 * (q : ℤ) + 1) + 1)).R = S ((q : ℤ) + 1) ∧
      (D.data (D.pha (m + 2 * (q : ℤ) + 1) + 1)).lo = lo ∧
      (D.data (D.pha (m + 2 * (q : ℤ) + 1) + 1)).hi = hi ∧
      (D.data (D.pha (m + 2 * (q : ℤ) + 2) + 1)).lo = 0 ∧
      (D.data (D.pha (m + 2 * (q : ℤ) + 2) + 1)).hi = 0)
    (hX0 : ∀ c, Xv A r₀ c m ∈ S 0) (p : ℕ) (hp : p ≤ k) :
    (∀ c, Xv A r₀ c (m + 2 * (p : ℤ)) ∈ S (p : ℤ)) ∧
      (∀ c, isL (Xv A r₀ c m) → Xv A r₀ c (m + 2 * (p : ℤ)) = Xv A r₀ c m) ∧
      (∀ c, isL (Xv A r₀ c (m + 2 * (p : ℤ))) → isL (Xv A r₀ c m)) := by
  induction p with
  | zero =>
    refine ⟨fun c => ?_, fun c h => ?_, fun c h => ?_⟩
    · rw [show m + 2 * ((0 : ℕ) : ℤ) = m by push_cast; ring]
      exact hX0 c
    · rw [show m + 2 * ((0 : ℕ) : ℤ) = m by push_cast; ring]
    · rw [show m + 2 * ((0 : ℕ) : ℤ) = m by push_cast; ring] at h
      exact h
  | succ q ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    obtain ⟨hR, hlo, hhi, hz1, hz2⟩ := hdata q (by omega)
    have hpar : (m + 2 * (q : ℤ)) % 2 = 0 := by omega
    -- the value at the odd time lies in the next set
    have hmid : ∀ c, Xv A r₀ c (m + 2 * (q : ℤ) + 1) ∈ S ((q : ℤ) + 1) := by
      intro c
      have h := memX_odd (c := c) (m := m + 2 * (q : ℤ) + 1) hr₀ (by omega)
      rw [hR] at h
      exact h
    have hint : ∀ c, lo ≤ Xv A r₀ c (m + 2 * (q : ℤ) + 1) - Xv A r₀ c (m + 2 * (q : ℤ)) ∧
        Xv A r₀ c (m + 2 * (q : ℤ) + 1) - Xv A r₀ c (m + 2 * (q : ℤ)) ≤ hi := by
      intro c
      have h := intv_even (c := c) (m := m + 2 * (q : ℤ)) hr₀ hpar
      rw [hlo, hhi] at h
      exact h
    -- the value does not change at the even step
    have hfix : ∀ c, Xv A r₀ c (m + 2 * (q : ℤ) + 2) = Xv A r₀ c (m + 2 * (q : ℤ) + 1) := by
      intro c
      have hy := intv_odd (c := c - 1) (m := m + 2 * (q : ℤ) + 1) hr₀ (by omega)
      rw [show m + 2 * (q : ℤ) + 1 + 1 = m + 2 * (q : ℤ) + 2 by ring, hz1, hz2] at hy
      have hpr := pair_odd (A := A) (r₀ := r₀) (c := c - 1) (m := m + 2 * (q : ℤ) + 1) (by omega)
      rw [show c - 1 + 1 = c by ring,
        show m + 2 * (q : ℤ) + 1 + 1 = m + 2 * (q : ℤ) + 2 by ring] at hpr
      omega
    have hcast : m + 2 * ((q + 1 : ℕ) : ℤ) = m + 2 * (q : ℤ) + 2 := by push_cast; ring
    have hq1 : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
    have hstep' : ∀ c, (isL (Xv A r₀ c (m + 2 * (q : ℤ))) →
          Xv A r₀ c (m + 2 * (q : ℤ) + 1) = Xv A r₀ c (m + 2 * (q : ℤ))) ∧
        (isL (Xv A r₀ c (m + 2 * (q : ℤ) + 1)) → isL (Xv A r₀ c (m + 2 * (q : ℤ)))) := by
      intro c
      refine hstep (q + 1) (by omega) (by omega) _ _ ?_ ?_ (hint c).1 (hint c).2
      · rw [hq1, show (q : ℤ) + 1 - 1 = (q : ℤ) by ring]
        exact ih1 c
      · rw [hq1]
        exact hmid c
    refine ⟨fun c => ?_, fun c h => ?_, fun c h => ?_⟩
    · rw [hcast, hfix c, hq1]
      exact hmid c
    · rw [hcast, hfix c, (hstep' c).1 (by rw [ih2 c h]; exact h), ih2 c h]
    · rw [hcast, hfix c] at h
      exact ih3 c ((hstep' c).2 h)


/-! ### One cycle of the buckets -/

section Cycle

variable {n : ℤ}

lemma sN_eq (D : ABData) : D.sN = 16 + 8 * D.P := rfl

lemma m0_even (D : ABData) (n : ℤ) : ((D.sN : ℤ) * n) % 2 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (D.sN : ℤ) = 2 * k := ⟨(D.sN : ℤ) / 2, by have := D.sN_even; omega⟩
  have h : (D.sN : ℤ) * n = 2 * (k * n) := by rw [hk]; ring
  omega

lemma even_at {j : ℕ} {m : ℤ} (hmj : m = (D.sN : ℤ) * n + (j : ℤ)) (hje : j % 2 = 0) :
    m % 2 = 0 := by
  have h1 := m0_even D n
  have h2 : ((j : ℕ) : ℤ) % 2 = 0 := by omega
  omega

/-- The bucket met at a given time of a cycle. -/
lemma data_at {j : ℕ} (hj : j < D.sN) {m : ℤ} (hmj : m = (D.sN : ℤ) * n + (j : ℤ))
    {q : ℕ} (hq : q = j + 1) : D.data (D.pha m + 1) = D.data q := by
  subst hq
  rw [hmj, (D.pha_add n j hj).1]

lemma memXv_of (hr₀ : A.st r₀ = 1) {j : ℕ} (hj : j < D.sN) (hje : j % 2 = 0) {m : ℤ}
    (hmj : m = (D.sN : ℤ) * n + (j : ℤ)) {R : Set ℤ} (hL : (D.data (j + 1)).L = R) (c : ℤ) :
    Xv A r₀ c m ∈ R := by
  have h := memX_even (c := c) (m := m) hr₀ (even_at hmj hje)
  rwa [data_at hj hmj rfl, hL] at h

lemma memYv_of (hr₀ : A.st r₀ = 1) {j : ℕ} (hj : j < D.sN) (hje : j % 2 = 0) {m : ℤ}
    (hmj : m = (D.sN : ℤ) * n + (j : ℤ)) {R : Set ℤ} (hR : (D.data (j + 1)).R = R) (c : ℤ) :
    Yv A r₀ c m ∈ R := by
  have h := memY_even (c := c) (m := m) hr₀ (even_at hmj hje)
  rwa [data_at hj hmj rfl, hR] at h

/-- A matching gadget sitting at the phase `j` of a cycle. -/
lemma match_at (hr₀ : A.st r₀ = 1) {g : ℤ → ℤ} (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1)
    {j : ℕ} (hj : j + 4 < D.sN) (hje : j % 2 = 0) {m : ℤ} (hmj : m = (D.sN : ℤ) * n + (j : ℤ))
    (hd1 : D.data (j + 1 + 1) = D.matchData g 1)
    (hd2 : D.data (j + 2 + 1) = D.matchData g 2)
    (hd3 : D.data (j + 3 + 1) = D.matchData g 3)
    (hd4 : D.data (j + 4 + 1) = D.matchData g 4)
    (hX : ∀ c, Xv A r₀ c m ∈ D.Eset) (hY : ∀ c, Yv A r₀ c m ∈ D.Eset) :
    (∀ c, Xv A r₀ c (m + 4) = Xv A r₀ c m) ∧
      (∀ c, g (Xv A r₀ (c + 1) m / D.d) - g (Xv A r₀ c m / D.d) = 2 * D.kz ∨
        g (Xv A r₀ (c + 1) m / D.d) - g (Xv A r₀ c m / D.d) ≤ -D.kz - 1) := by
  refine match_gadget hr₀ hgb (even_at hmj hje) ?_ ?_ ?_ ?_ hX hY
  · exact (data_at (n := n) (j := j + 1) (by omega) (by rw [hmj]; push_cast; ring) rfl).trans hd1
  · exact (data_at (n := n) (j := j + 2) (by omega) (by rw [hmj]; push_cast; ring) rfl).trans hd2
  · exact (data_at (n := n) (j := j + 3) (by omega) (by rw [hmj]; push_cast; ring) rfl).trans hd3
  · exact (data_at (n := n) (j := j + 4) (by omega) (by rw [hmj]; push_cast; ring) rfl).trans hd4


/-! ### The two free gadgets -/

/-- The first free gadget, between the phases `8` and `8 + 4P` of a cycle: the `A` indices do not
move, and no value becomes an `A` index. -/
lemma free1 (hr₀ : A.st r₀ = 1) (n : ℤ)
    (hX8 : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 8) ∈ D.Eset) :
    (∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) ∈ D.Eset) ∧
      (∀ c, D.isA (Xv A r₀ c ((D.sN : ℤ) * n + 8)) →
        Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) = Xv A r₀ c ((D.sN : ℤ) * n + 8)) ∧
      (∀ c, D.isA (Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ))) →
        D.isA (Xv A r₀ c ((D.sN : ℤ) * n + 8))) := by
  have hsN := sN_eq D
  have hP : 1 ≤ D.P := Nat.le_max_right _ _
  -- the compression half
  have hdata1 : ∀ q : ℕ, q < D.P →
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 1) + 1)).R = D.C₁ ((q : ℤ) + 1) ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 1) + 1)).lo = -D.d + 1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 1) + 1)).hi = 1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 2) + 1)).lo = 0 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 2) + 1)).hi = 0 := by
    intro q hq
    have h1 : (D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 1 = (D.sN : ℤ) * n + ((9 + 2 * q : ℕ) : ℤ) := by
      push_cast; ring
    have h2 : (D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 2 = (D.sN : ℤ) * n + ((10 + 2 * q : ℕ) : ℤ) := by
      push_cast; ring
    have e1 : D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 1) + 1)
        = D.freeData₁ (2 * (q + 1) - 1) := by
      rw [data_at (n := n) (j := 9 + 2 * q) (by omega) h1 rfl,
        show 9 + 2 * q + 1 = 9 + (2 * (q + 1) - 1) by omega,
        D.data_f1 (2 * (q + 1) - 1) (by omega) (by omega)]
    have e2 : D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (q : ℤ) + 2) + 1)
        = D.freeData₁ (2 * (q + 1)) := by
      rw [data_at (n := n) (j := 10 + 2 * q) (by omega) h2 rfl,
        show 10 + 2 * q + 1 = 9 + 2 * (q + 1) by omega,
        D.data_f1 (2 * (q + 1)) (by omega) (by omega)]
    rw [e1, e2, D.freeData₁_odd (q + 1) (by omega) (by omega),
      D.freeData₁_even (q + 1) (by omega)]
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    norm_cast
  have hcomp := free_half (A := A) (r₀ := r₀) (S := D.C₁) (isL := D.isA)
    (lo := -D.d + 1) (hi := 1) (k := D.P) (m := (D.sN : ℤ) * n + 8) hr₀
    (even_at (D := D) (n := n) (j := 8) (by norm_num) (by norm_num))
    (fun q hq1 _ u u' hu hu' h1 h2 => D.C₁_step (by exact_mod_cast hq1) hu hu' h1 h2)
    hdata1 (fun c => by rw [D.C₁_zero]; exact hX8 c) D.P le_rfl
  -- the expansion half
  have hdata2 : ∀ q : ℕ, q < D.P →
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)).R
          = D.D₁ ((q : ℤ) + 1) ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)).lo = -1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)).hi = D.d - 1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2) + 1)).lo = 0 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2) + 1)).hi = 0 := by
    intro q hq
    have h1 : (D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 1
        = (D.sN : ℤ) * n + ((9 + 2 * D.P + 2 * q : ℕ) : ℤ) := by push_cast; ring
    have h2 : (D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2
        = (D.sN : ℤ) * n + ((10 + 2 * D.P + 2 * q : ℕ) : ℤ) := by push_cast; ring
    have e1 : D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)
        = D.freeData₁ (2 * D.P + 2 * (q + 1) - 1) := by
      rw [data_at (n := n) (j := 9 + 2 * D.P + 2 * q) (by omega) h1 rfl,
        show 9 + 2 * D.P + 2 * q + 1 = 9 + (2 * D.P + 2 * (q + 1) - 1) by omega,
        D.data_f1 (2 * D.P + 2 * (q + 1) - 1) (by omega) (by omega)]
    have e2 : D.data (D.pha ((D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2) + 1)
        = D.freeData₁ (2 * D.P + 2 * (q + 1)) := by
      rw [data_at (n := n) (j := 10 + 2 * D.P + 2 * q) (by omega) h2 rfl,
        show 10 + 2 * D.P + 2 * q + 1 = 9 + (2 * D.P + 2 * (q + 1)) by omega,
        D.data_f1 (2 * D.P + 2 * (q + 1)) (by omega) (by omega)]
    rw [e1, e2, D.freeData₁_exp_odd (q + 1) (by omega)]
    refine ⟨by norm_cast, rfl, rfl, ?_, ?_⟩ <;>
      rcases lt_or_eq_of_le (show q + 1 ≤ D.P by omega) with hlt | heq
    · rw [D.freeData₁_exp_even (q + 1) (by omega) hlt]
    · rw [show 2 * D.P + 2 * (q + 1) = 4 * D.P by omega, D.freeData₁_last]
    · rw [D.freeData₁_exp_even (q + 1) (by omega) hlt]
    · rw [show 2 * D.P + 2 * (q + 1) = 4 * D.P by omega, D.freeData₁_last]
  have hexp := free_half (A := A) (r₀ := r₀) (S := D.D₁) (isL := D.isA)
    (lo := -1) (hi := D.d - 1) (k := D.P) (m := (D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ)) hr₀
    (even_at (D := D) (n := n) (j := 8 + 2 * D.P) (by push_cast; ring) (by omega))
    (fun q _ hq2 u u' hu hu' h1 h2 => D.D₁_step
      (show ((q : ℕ) : ℤ) ≤ D.pz from
        by have h : ((q : ℕ) : ℤ) ≤ ((D.P : ℕ) : ℤ) := by exact_mod_cast hq2
           exact h) hu hu' h1 h2)
    hdata2
    (fun c => by
      have h := hcomp.1 c
      rwa [show D.C₁ ((D.P : ℕ) : ℤ) = D.D₁ 0 from D.C₁_top_eq_D₁_zero] at h)
    D.P le_rfl
  rw [show (D.sN : ℤ) * n + 8 + 2 * (D.P : ℤ) + 2 * (D.P : ℤ)
      = (D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ) by ring] at hexp
  refine ⟨fun c => ?_, fun c h => ?_, fun c h => ?_⟩
  · have := hexp.1 c
    rwa [show D.D₁ ((D.P : ℕ) : ℤ) = D.Eset from D.D₁_top] at this
  · rw [hexp.2.1 c (by rw [hcomp.2.1 c h]; exact h), hcomp.2.1 c h]
  · exact hcomp.2.2 c (hexp.2.2 c h)

/-- The second free gadget, between the phases `16 + 4P` and `s` of a cycle: the `B` indices do
not move, and no value becomes a `B` index. -/
lemma free2 (hr₀ : A.st r₀ = 1) (n : ℤ)
    (hX : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ)) ∈ D.Eset) :
    (∀ c, Xv A r₀ c ((D.sN : ℤ) * (n + 1)) ∈ D.Eset) ∧
      (∀ c, D.isB (Xv A r₀ c ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ))) →
        Xv A r₀ c ((D.sN : ℤ) * (n + 1))
          = Xv A r₀ c ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ))) ∧
      (∀ c, D.isB (Xv A r₀ c ((D.sN : ℤ) * (n + 1))) →
        D.isB (Xv A r₀ c ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ)))) := by
  have hsN := sN_eq D
  have hP : 1 ≤ D.P := Nat.le_max_right _ _
  have hsz : ((D.sN : ℕ) : ℤ) = 16 + 8 * ((D.P : ℕ) : ℤ) := by rw [hsN]; push_cast; ring
  -- the compression half
  have hdata1 : ∀ q : ℕ, q < D.P →
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)).R
          = D.C₂ ((q : ℤ) + 1) ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)).lo = -1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)).hi = D.d - 1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 2) + 1)).lo = 0 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 2) + 1)).hi = 0 := by
    intro q hq
    have h1 : (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 1
        = (D.sN : ℤ) * n + ((17 + 4 * D.P + 2 * q : ℕ) : ℤ) := by push_cast; ring
    have h2 : (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 2
        = (D.sN : ℤ) * n + ((18 + 4 * D.P + 2 * q : ℕ) : ℤ) := by push_cast; ring
    have e1 : D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 1) + 1)
        = D.freeData₂ (2 * (q + 1) - 1) := by
      rw [data_at (n := n) (j := 17 + 4 * D.P + 2 * q) (by omega) h1 rfl,
        show 17 + 4 * D.P + 2 * q + 1 = 17 + 4 * D.P + (2 * (q + 1) - 1) by omega,
        D.data_f2 (2 * (q + 1) - 1) (by omega) (by omega)]
    have e2 : D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (q : ℤ) + 2) + 1)
        = D.freeData₂ (2 * (q + 1)) := by
      rw [data_at (n := n) (j := 18 + 4 * D.P + 2 * q) (by omega) h2 rfl,
        show 18 + 4 * D.P + 2 * q + 1 = 17 + 4 * D.P + 2 * (q + 1) by omega,
        D.data_f2 (2 * (q + 1)) (by omega) (by omega)]
    rw [e1, e2, D.freeData₂_odd (q + 1) (by omega) (by omega),
      D.freeData₂_even (q + 1) (by omega)]
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    norm_cast
  have hcomp := free_half (A := A) (r₀ := r₀) (S := D.C₂) (isL := D.isB)
    (lo := -1) (hi := D.d - 1) (k := D.P) (m := (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ)) hr₀
    (even_at (D := D) (n := n) (j := 16 + 4 * D.P) (by push_cast; ring) (by omega))
    (fun q hq1 _ u u' hu hu' h1 h2 => D.C₂_step (by exact_mod_cast hq1) hu hu' h1 h2)
    hdata1 (fun c => by rw [D.C₂_zero]; exact hX c) D.P le_rfl
  -- the expansion half
  have hdata2 : ∀ q : ℕ, q < D.P →
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ)
          + 2 * (q : ℤ) + 1) + 1)).R = D.D₂ ((q : ℤ) + 1) ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ)
          + 2 * (q : ℤ) + 1) + 1)).lo = -D.d + 1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ)
          + 2 * (q : ℤ) + 1) + 1)).hi = 1 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ)
          + 2 * (q : ℤ) + 2) + 1)).lo = 0 ∧
      (D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ)
          + 2 * (q : ℤ) + 2) + 1)).hi = 0 := by
    intro q hq
    have h1 : (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 1
        = (D.sN : ℤ) * n + ((17 + 6 * D.P + 2 * q : ℕ) : ℤ) := by push_cast; ring
    have e1 : D.data (D.pha ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ)
        + 2 * (q : ℤ) + 1) + 1) = D.freeData₂ (2 * D.P + 2 * (q + 1) - 1) := by
      rw [data_at (n := n) (j := 17 + 6 * D.P + 2 * q) (by omega) h1 rfl,
        show 17 + 6 * D.P + 2 * q + 1 = 17 + 4 * D.P + (2 * D.P + 2 * (q + 1) - 1) by omega,
        D.data_f2 (2 * D.P + 2 * (q + 1) - 1) (by omega) (by omega)]
    rw [e1, D.freeData₂_exp_odd (q + 1) (by omega)]
    refine ⟨by norm_cast, rfl, rfl, ?_, ?_⟩ <;>
      rcases lt_or_eq_of_le (show q + 1 ≤ D.P by omega) with hlt | heq
    · rw [show (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2
          = (D.sN : ℤ) * n + ((18 + 6 * D.P + 2 * q : ℕ) : ℤ) by push_cast; ring]
      rw [data_at (n := n) (j := 18 + 6 * D.P + 2 * q) (by omega) rfl rfl,
        show 18 + 6 * D.P + 2 * q + 1 = 17 + 4 * D.P + (2 * D.P + 2 * (q + 1)) by omega,
        D.data_f2 (2 * D.P + 2 * (q + 1)) (by omega) (by omega),
        D.freeData₂_exp_even (q + 1) (by omega)]
    · rw [show (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2
          = (D.sN : ℤ) * (n + 1) by
        have hq2 : ((q : ℕ) : ℤ) = ((D.P : ℕ) : ℤ) - 1 := by
          have : (q : ℕ) + 1 = D.P := heq
          push_cast [← this]; ring
        rw [hq2, hsz]; ring]
      rw [(D.pha_mul (n + 1)).1]
      show (D.data 1).lo = 0
      rw [D.data_one]
    · rw [show (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2
          = (D.sN : ℤ) * n + ((18 + 6 * D.P + 2 * q : ℕ) : ℤ) by push_cast; ring]
      rw [data_at (n := n) (j := 18 + 6 * D.P + 2 * q) (by omega) rfl rfl,
        show 18 + 6 * D.P + 2 * q + 1 = 17 + 4 * D.P + (2 * D.P + 2 * (q + 1)) by omega,
        D.data_f2 (2 * D.P + 2 * (q + 1)) (by omega) (by omega),
        D.freeData₂_exp_even (q + 1) (by omega)]
    · rw [show (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ) + 2 * (q : ℤ) + 2
          = (D.sN : ℤ) * (n + 1) by
        have hq2 : ((q : ℕ) : ℤ) = ((D.P : ℕ) : ℤ) - 1 := by
          have : (q : ℕ) + 1 = D.P := heq
          push_cast [← this]; ring
        rw [hq2, hsz]; ring]
      rw [(D.pha_mul (n + 1)).1]
      show (D.data 1).hi = 0
      rw [D.data_one]
  have hexp := free_half (A := A) (r₀ := r₀) (S := D.D₂) (isL := D.isB)
    (lo := -D.d + 1) (hi := 1) (k := D.P)
    (m := (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ)) hr₀
    (even_at (D := D) (n := n) (j := 16 + 6 * D.P) (by push_cast; ring) (by omega))
    (fun q _ hq2 u u' hu hu' h1 h2 => D.D₂_step
      (show ((q : ℕ) : ℤ) ≤ D.pz from
        by have h : ((q : ℕ) : ℤ) ≤ ((D.P : ℕ) : ℤ) := by exact_mod_cast hq2
           exact h) hu hu' h1 h2)
    hdata2
    (fun c => by
      have h := hcomp.1 c
      rwa [show D.C₂ ((D.P : ℕ) : ℤ) = D.D₂ 0 from D.C₂_top_eq_D₂_zero] at h)
    D.P le_rfl
  rw [show (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ) + 2 * (D.P : ℤ) + 2 * (D.P : ℤ)
      = (D.sN : ℤ) * (n + 1) by rw [hsz]; ring] at hexp
  refine ⟨fun c => ?_, fun c h => ?_, fun c h => ?_⟩
  · have := hexp.1 c
    rwa [show D.D₂ ((D.P : ℕ) : ℤ) = D.Eset from D.D₂_top] at this
  · rw [hexp.2.1 c (by rw [hcomp.2.1 c h]; exact h), hcomp.2.1 c h]
  · exact hcomp.2.2 c (hexp.2.2 c h)


/-! ### One whole cycle -/

/-- The index of the tile carried by the column `c` at the bottom of the band `n`. -/
def idx (A : LineAssignment D.spec) (r₀ : ℤ) (c n : ℤ) : ℤ := Xv A r₀ c ((D.sN : ℤ) * n) / D.d

/-- The index of the tile carried by the column `c` in the middle of the band `n`. -/
def jdx (A : LineAssignment D.spec) (r₀ : ℤ) (c n : ℤ) : ℤ :=
  Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) / D.d

/-- Everything one cycle of the buckets forces: the four alternation conditions of the four
matching gadgets, and the two locking conditions of the two free gadgets. -/
lemma cycle_facts (hr₀ : A.st r₀ = 1) (n : ℤ) :
    (∀ c, Xv A r₀ c ((D.sN : ℤ) * n) ∈ D.Eset) ∧
    (∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) ∈ D.Eset) ∧
    (∀ c, D.g₁ (idx A r₀ (c + 1) n) - D.g₁ (idx A r₀ c n) = 2 * D.kz ∨
      D.g₁ (idx A r₀ (c + 1) n) - D.g₁ (idx A r₀ c n) ≤ -D.kz - 1) ∧
    (∀ c, D.g₂ (idx A r₀ (c + 1) n) - D.g₂ (idx A r₀ c n) = 2 * D.kz ∨
      D.g₂ (idx A r₀ (c + 1) n) - D.g₂ (idx A r₀ c n) ≤ -D.kz - 1) ∧
    (∀ c, D.g₃ (jdx A r₀ (c + 1) n) - D.g₃ (jdx A r₀ c n) = 2 * D.kz ∨
      D.g₃ (jdx A r₀ (c + 1) n) - D.g₃ (jdx A r₀ c n) ≤ -D.kz - 1) ∧
    (∀ c, D.g₄ (jdx A r₀ (c + 1) n) - D.g₄ (jdx A r₀ c n) = 2 * D.kz ∨
      D.g₄ (jdx A r₀ (c + 1) n) - D.g₄ (jdx A r₀ c n) ≤ -D.kz - 1) ∧
    (∀ c, D.isA (Xv A r₀ c ((D.sN : ℤ) * n)) →
      Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) = Xv A r₀ c ((D.sN : ℤ) * n)) ∧
    (∀ c, D.isA (Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ))) →
      D.isA (Xv A r₀ c ((D.sN : ℤ) * n))) ∧
    (∀ c, D.isB (Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ))) →
      Xv A r₀ c ((D.sN : ℤ) * (n + 1)) = Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ))) ∧
    (∀ c, D.isB (Xv A r₀ c ((D.sN : ℤ) * (n + 1))) →
      D.isB (Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)))) := by
  have hsN := sN_eq D
  have hP : 1 ≤ D.P := Nat.le_max_right _ _
  -- the encoding row at the bottom of the band
  have hXbot : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n) ∈ D.Eset := by
    refine memXv_of (D := D) (n := n) hr₀ (j := 0) (by omega) (by norm_num)
      (m := (D.sN : ℤ) * n) (by norm_num) ?_
    show (D.data 1).L = D.Eset
    rw [D.data_one]
  have hYbot : ∀ c, Yv A r₀ c ((D.sN : ℤ) * n) ∈ D.Eset := by
    refine memYv_of (D := D) (n := n) hr₀ (j := 0) (by omega) (by norm_num)
      (m := (D.sN : ℤ) * n) (by norm_num) ?_
    show (D.data 1).R = D.Eset
    rw [D.data_one]
  -- the first matching gadget
  have hg1 := match_at (D := D) (n := n) hr₀ D.g₁_bounds (j := 0) (by omega) (by norm_num)
    (m := (D.sN : ℤ) * n) (by norm_num)
    (D.data_m1 1 (by omega) (by omega)) (D.data_m1 2 (by omega) (by omega))
    (D.data_m1 3 (by omega) (by omega)) (D.data_m1 4 (by omega) (by omega)) hXbot hYbot
  -- the second matching gadget
  have hX4 : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 4) ∈ D.Eset := fun c => by
    rw [hg1.1 c]; exact hXbot c
  have hY4 : ∀ c, Yv A r₀ c ((D.sN : ℤ) * n + 4) ∈ D.Eset := by
    refine memYv_of (D := D) (n := n) hr₀ (j := 4) (by omega) (by norm_num)
      (m := (D.sN : ℤ) * n + 4) (by norm_num) ?_
    rw [show D.data (4 + 1) = D.matchData D.g₁ 4 from D.data_m1 4 (by omega) (by omega),
      D.matchData_four]
  have hg2 := match_at (D := D) (n := n) hr₀ D.g₂_bounds (j := 4) (by omega) (by norm_num)
    (m := (D.sN : ℤ) * n + 4) (by norm_num)
    (D.data_m2 1 (by omega) (by omega)) (D.data_m2 2 (by omega) (by omega))
    (D.data_m2 3 (by omega) (by omega)) (D.data_m2 4 (by omega) (by omega)) hX4 hY4
  -- the first free gadget
  have hX8 : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 8) ∈ D.Eset := fun c => by
    rw [show (D.sN : ℤ) * n + 8 = (D.sN : ℤ) * n + 4 + 4 by ring, hg2.1 c]
    exact hX4 c
  have hX8eq : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 8) = Xv A r₀ c ((D.sN : ℤ) * n) := fun c => by
    rw [show (D.sN : ℤ) * n + 8 = (D.sN : ℤ) * n + 4 + 4 by ring, hg2.1 c, hg1.1 c]
  have hf1 := free1 hr₀ n hX8
  -- the encoding row in the middle of the band
  have hXmid : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) ∈ D.Eset := hf1.1
  have hYmid : ∀ c, Yv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) ∈ D.Eset := by
    refine memYv_of (D := D) (n := n) hr₀ (j := 8 + 4 * D.P) (by omega) (by omega)
      (m := (D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) (by push_cast; ring) ?_
    rw [show 8 + 4 * D.P + 1 = 9 + 4 * D.P by omega,
      D.data_f1 (4 * D.P) (by omega) (by omega), D.freeData₁_last]
  -- the third matching gadget
  have hg3 := match_at (D := D) (n := n) hr₀ D.g₃_bounds (j := 8 + 4 * D.P) (by omega) (by omega)
    (m := (D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) (by push_cast; ring)
    (by rw [show 8 + 4 * D.P + 1 + 1 = 9 + 4 * D.P + 1 by omega]
        exact D.data_m3 1 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 2 + 1 = 9 + 4 * D.P + 2 by omega]
        exact D.data_m3 2 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 3 + 1 = 9 + 4 * D.P + 3 by omega]
        exact D.data_m3 3 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 4 + 1 = 9 + 4 * D.P + 4 by omega]
        exact D.data_m3 4 (by omega) (by omega))
    hXmid hYmid
  -- the fourth matching gadget
  have hXmid4 : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ) + 4) ∈ D.Eset := fun c => by
    rw [hg3.1 c]; exact hXmid c
  have hYmid4 : ∀ c, Yv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ) + 4) ∈ D.Eset := by
    refine memYv_of (D := D) (n := n) hr₀ (j := 12 + 4 * D.P) (by omega) (by omega)
      (m := (D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ) + 4) (by push_cast; ring) ?_
    rw [show 12 + 4 * D.P + 1 = 9 + 4 * D.P + 4 by omega,
      D.data_m3 4 (by omega) (by omega), D.matchData_four]
  have hg4 := match_at (D := D) (n := n) hr₀ D.g₄_bounds (j := 12 + 4 * D.P) (by omega) (by omega)
    (m := (D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ) + 4) (by push_cast; ring)
    (by rw [show 12 + 4 * D.P + 1 + 1 = 13 + 4 * D.P + 1 by omega]
        exact D.data_m4 1 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 2 + 1 = 13 + 4 * D.P + 2 by omega]
        exact D.data_m4 2 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 3 + 1 = 13 + 4 * D.P + 3 by omega]
        exact D.data_m4 3 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 4 + 1 = 13 + 4 * D.P + 4 by omega]
        exact D.data_m4 4 (by omega) (by omega))
    hXmid4 hYmid4
  -- the second free gadget
  have hXfree2 : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ)) ∈ D.Eset := fun c => by
    rw [show (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ)
        = (D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ) + 4 + 4 by ring, hg4.1 c]
    exact hXmid4 c
  have hXfree2eq : ∀ c, Xv A r₀ c ((D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ))
      = Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) := fun c => by
    rw [show (D.sN : ℤ) * n + 16 + 4 * (D.P : ℤ)
        = (D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ) + 4 + 4 by ring, hg4.1 c, hg3.1 c]
  have hf2 := free2 hr₀ n hXfree2
  refine ⟨hXbot, hXmid, hg1.2, ?_, hg3.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    have h := hg2.2 c
    rw [hg1.1 c, hg1.1 (c + 1)] at h
    exact h
  · intro c
    have h := hg4.2 c
    rw [hg3.1 c, hg3.1 (c + 1)] at h
    exact h
  · intro c h
    rw [hf1.2.1 c (by rw [hX8eq c]; exact h), hX8eq c]
  · intro c h
    have := hf1.2.2 c h
    rwa [hX8eq c] at this
  · intro c h
    rw [hf2.2.1 c (by rw [hXfree2eq c]; exact h), hXfree2eq c]
  · intro c h
    have := hf2.2.2 c h
    rwa [hXfree2eq c] at this

end Cycle

end Backward

end ABSim

end StickPolyhex
