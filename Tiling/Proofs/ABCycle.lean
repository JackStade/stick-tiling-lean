import Tiling.Proofs.ABPhases

/-!
# Cycles and phases

Both directions of the proof of Sections 2.6–2.8 read the rows of a gap assignment through the
*time* `m`, the number of rows one has gone down from a fixed reference row.  The state of the
row at time `m` is the bucket number `1 + (m mod s)`; the *phase* `ABData.pha m` is that
remainder and the *cycle* `ABData.cyc m` is the quotient, so that `m = s * cyc m + pha m`.  This
file collects the arithmetic of these two functions.
-/

namespace StickPolyhex

namespace ABSim

namespace ABData

variable (D : ABData)

/-- The cycle of the time `m`: how many complete runs through the buckets have been made. -/
def cyc (m : ℤ) : ℤ := m / (D.sN : ℤ)

/-- The phase of the time `m`: the position inside the current run through the buckets. -/
def pha (m : ℤ) : ℕ := (m % (D.sN : ℤ)).toNat

lemma sN_pos : 0 < (D.sN : ℤ) := by
  have := D.sixteen_le_sN; exact_mod_cast (by omega : 0 < D.sN)

lemma pha_cast (m : ℤ) : ((D.pha m : ℕ) : ℤ) = m % (D.sN : ℤ) := by
  have := Int.emod_nonneg m (by have := D.sN_pos; omega : (D.sN : ℤ) ≠ 0)
  simp only [pha]
  omega

lemma pha_lt (m : ℤ) : D.pha m < D.sN := by
  have h1 := D.pha_cast m
  have h2 := Int.emod_lt_of_pos m D.sN_pos
  omega

lemma decomp (m : ℤ) : (D.sN : ℤ) * D.cyc m + (D.pha m : ℤ) = m := by
  have := Int.emod_add_mul_ediv m (D.sN : ℤ)
  rw [D.pha_cast m]
  simp only [cyc]
  omega

/-- Stepping one row down advances the phase, cyclically. -/
lemma pha_succ_lt {m : ℤ} (h : D.pha m + 1 < D.sN) :
    D.pha (m + 1) = D.pha m + 1 ∧ D.cyc (m + 1) = D.cyc m := by
  have hs := D.sN_pos
  have h1 := Int.emod_add_mul_ediv m (D.sN : ℤ)
  have h2 := Int.emod_nonneg m (by omega : (D.sN : ℤ) ≠ 0)
  have hc := D.pha_cast m
  have hlt : m % (D.sN : ℤ) + 1 < (D.sN : ℤ) := by
    have : ((D.pha m : ℕ) : ℤ) + 1 < (D.sN : ℤ) := by exact_mod_cast h
    omega
  have key := (Int.ediv_emod_unique (a := m + 1) (b := (D.sN : ℤ))
    (r := m % (D.sN : ℤ) + 1) (q := m / (D.sN : ℤ)) hs).mpr ⟨by omega, by omega, by omega⟩
  refine ⟨?_, key.1⟩
  have : ((D.pha (m + 1) : ℕ) : ℤ) = ((D.pha m : ℕ) : ℤ) + 1 := by
    rw [D.pha_cast, key.2, hc]
  exact_mod_cast this

/-- Stepping one row down from the last bucket starts a new cycle. -/
lemma pha_succ_eq {m : ℤ} (h : D.pha m + 1 = D.sN) :
    D.pha (m + 1) = 0 ∧ D.cyc (m + 1) = D.cyc m + 1 := by
  have hs := D.sN_pos
  have h1 := Int.emod_add_mul_ediv m (D.sN : ℤ)
  have h2 := Int.emod_nonneg m (by omega : (D.sN : ℤ) ≠ 0)
  have hc := D.pha_cast m
  have heq : m % (D.sN : ℤ) + 1 = (D.sN : ℤ) := by
    have : ((D.pha m : ℕ) : ℤ) + 1 = (D.sN : ℤ) := by exact_mod_cast h
    omega
  have key := (Int.ediv_emod_unique (a := m + 1) (b := (D.sN : ℤ))
    (r := 0) (q := m / (D.sN : ℤ) + 1) hs).mpr ⟨by nlinarith, by omega, by omega⟩
  refine ⟨?_, key.1⟩
  have : ((D.pha (m + 1) : ℕ) : ℤ) = 0 := by rw [D.pha_cast, key.2]
  exact_mod_cast this

/-- The phase at a multiple of the length of the cycle is `0`. -/
lemma pha_mul (n : ℤ) : D.pha ((D.sN : ℤ) * n) = 0 ∧ D.cyc ((D.sN : ℤ) * n) = n := by
  have hs := D.sN_pos
  have key := (Int.ediv_emod_unique (a := (D.sN : ℤ) * n) (b := (D.sN : ℤ))
    (r := 0) (q := n) hs).mpr ⟨by ring, by omega, by omega⟩
  refine ⟨?_, key.1⟩
  have : ((D.pha ((D.sN : ℤ) * n) : ℕ) : ℤ) = 0 := by rw [D.pha_cast, key.2]
  exact_mod_cast this

/-- Adding a phase to a multiple of the length of the cycle. -/
lemma pha_add (n : ℤ) (j : ℕ) (hj : j < D.sN) :
    D.pha ((D.sN : ℤ) * n + (j : ℤ)) = j ∧ D.cyc ((D.sN : ℤ) * n + (j : ℤ)) = n := by
  have hs := D.sN_pos
  have hj' : (j : ℤ) < (D.sN : ℤ) := by exact_mod_cast hj
  have key := (Int.ediv_emod_unique (a := (D.sN : ℤ) * n + (j : ℤ)) (b := (D.sN : ℤ))
    (r := (j : ℤ)) (q := n) hs).mpr ⟨by ring, by omega, by omega⟩
  refine ⟨?_, key.1⟩
  have : ((D.pha ((D.sN : ℤ) * n + (j : ℤ)) : ℕ) : ℤ) = (j : ℤ) := by rw [D.pha_cast, key.2]
  exact_mod_cast this

/-- The phase has the same parity as the time, because the cycle has even length. -/
lemma even_iff_pha_even (m : ℤ) : Even m ↔ D.pha m % 2 = 0 := by
  have hd := D.decomp m
  have hs : D.sN % 2 = 0 := D.sN_even
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (D.sN : ℤ) = 2 * k := ⟨(D.sN : ℤ) / 2, by omega⟩
  have hm : m = 2 * (k * D.cyc m) + ((D.pha m : ℕ) : ℤ) := by
    rw [hk] at hd; linear_combination -hd
  constructor
  · rintro ⟨j, hj⟩
    have : ((D.pha m : ℕ) : ℤ) % 2 = 0 := by omega
    omega
  · intro h
    have : ((D.pha m : ℕ) : ℤ) % 2 = 0 := by omega
    exact ⟨k * D.cyc m + ((D.pha m : ℕ) : ℤ) / 2, by omega⟩

end ABData

end ABSim

end StickPolyhex
