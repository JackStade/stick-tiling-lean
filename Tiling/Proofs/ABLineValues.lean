import Tiling.Proofs.ABValues
import Tiling.Proofs.ABIndex

/-!
# The line values built from an index tiling

Given an index tiling, this file defines the value `IndexTiling.xphase c n j` carried in the
phase `j` of the cycle `n` by the line of gaps of the column `c`, and the displacement
`IndexTiling.cphase c n j` of the line of gaps between the columns `c` and `c + 1`; the value of
that second line is `IndexTiling.yphase c n j = v - xphase c n j + cphase c n j`.

The lines of even index are the lines of the columns, the lines of odd index are the lines
between two columns; the sum of the values of the two lines bounding a gap is the constant `v`,
up to the displacement, which is nonzero only in the middle of a matching gadget.

The bulk of the file is the list of evaluations of `xphase` and `cphase` in each of the gadgets,
which is what the verification of the gap conditions in `Tiling/Proofs/ABForward.lean` uses.
-/

namespace StickPolyhex

namespace ABSim

namespace IndexTiling

variable {D : ABData} (T : IndexTiling D)

/-! ### The indices of a column -/

lemma ix_one_le (c n : ℤ) : 1 ≤ T.ix c n := (T.ix_mem c n).1

lemma ix_le (c n : ℤ) : T.ix c n ≤ 2 * D.tz := (T.ix_mem c n).2

lemma ix_A (c n : ℤ) (h : c % 2 = 0) : T.ix c n ≤ D.tz :=
  T.ix_even c n (Int.even_iff.2 h)

lemma ix_B (c n : ℤ) (h : ¬ c % 2 = 0) : D.tz < T.ix c n :=
  T.ix_odd c n (fun he => h (Int.even_iff.1 he))

lemma lockA' (c n : ℤ) (h : c % 2 = 0) : T.jx c n = T.ix c n :=
  T.lockA c n (Int.even_iff.2 h)

lemma lockB' (c n : ℤ) (h : ¬ c % 2 = 0) : T.jx c n = T.ix c (n + 1) :=
  T.lockB c n (fun he => h (Int.even_iff.1 he))

lemma jx_one_le (c n : ℤ) : 1 ≤ T.jx c n := by
  by_cases h : c % 2 = 0
  · rw [T.lockA' c n h]; exact T.ix_one_le c n
  · rw [T.lockB' c n h]; exact T.ix_one_le c (n + 1)

lemma jx_le (c n : ℤ) : T.jx c n ≤ 2 * D.tz := by
  by_cases h : c % 2 = 0
  · rw [T.lockA' c n h]; exact T.ix_le c n
  · rw [T.lockB' c n h]; exact T.ix_le c (n + 1)

lemma jx_A (c n : ℤ) (h : c % 2 = 0) : T.jx c n ≤ D.tz := by
  rw [T.lockA' c n h]; exact T.ix_A c n h

lemma jx_B (c n : ℤ) (h : ¬ c % 2 = 0) : D.tz < T.jx c n := by
  rw [T.lockB' c n h]; exact T.ix_B c (n + 1) h

/-! ### The values -/

/-- The value carried in the phase `j` of the cycle `n` by the line of the column `c`. -/
def xphase (c n : ℤ) (j : ℕ) : ℤ :=
  if j ≤ 4 then D.mxv D.g₁ (T.ix c n) j
  else if j ≤ 8 then D.mxv D.g₂ (T.ix c n) (j - 4)
  else if j ≤ 8 + 2 * D.P then D.comp1 c (T.ix c n) (((j - 7) / 2 : ℕ) : ℤ)
  else if j ≤ 8 + 4 * D.P then D.exp1 c (T.jx c n) (((j - 7 - 2 * D.P) / 2 : ℕ) : ℤ)
  else if j ≤ 12 + 4 * D.P then D.mxv D.g₃ (T.jx c n) (j - 8 - 4 * D.P)
  else if j ≤ 16 + 4 * D.P then D.mxv D.g₄ (T.jx c n) (j - 12 - 4 * D.P)
  else if j ≤ 16 + 6 * D.P then D.comp2 c (T.jx c n) (((j - 15 - 4 * D.P) / 2 : ℕ) : ℤ)
  else D.exp2 c (T.ix c (n + 1)) (((j - 15 - 6 * D.P) / 2 : ℕ) : ℤ)

/-- The displacement of the line of gaps between the columns `c` and `c + 1`. -/
def cphase (c n : ℤ) (j : ℕ) : ℤ :=
  if j ≤ 4 then mcorr D.g₁ (T.ix c n) (T.ix (c + 1) n) j
  else if j ≤ 8 then mcorr D.g₂ (T.ix c n) (T.ix (c + 1) n) (j - 4)
  else if j ≤ 8 + 4 * D.P then 0
  else if j ≤ 12 + 4 * D.P then mcorr D.g₃ (T.jx c n) (T.jx (c + 1) n) (j - 8 - 4 * D.P)
  else if j ≤ 16 + 4 * D.P then mcorr D.g₄ (T.jx c n) (T.jx (c + 1) n) (j - 12 - 4 * D.P)
  else 0

/-- The value carried by the line of gaps between the columns `c` and `c + 1`. -/
def yphase (c n : ℤ) (j : ℕ) : ℤ := D.vz - T.xphase c n j + T.cphase c n j

/-! ### Evaluation inside the first two matching gadgets -/

lemma xphase_m1 (c n : ℤ) (i : ℕ) (hi : i ≤ 4) :
    T.xphase c n i = D.mxv D.g₁ (T.ix c n) i := by
  unfold xphase; rw [if_pos hi]

lemma cphase_m1 (c n : ℤ) (i : ℕ) (hi : i ≤ 4) :
    T.cphase c n i = mcorr D.g₁ (T.ix c n) (T.ix (c + 1) n) i := by
  unfold cphase; rw [if_pos hi]

lemma xphase_m2 (c n : ℤ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ 4) :
    T.xphase c n (4 + i) = D.mxv D.g₂ (T.ix c n) i := by
  unfold xphase
  rw [if_neg (by omega), if_pos (by omega), show 4 + i - 4 = i by omega]

lemma cphase_m2 (c n : ℤ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ 4) :
    T.cphase c n (4 + i) = mcorr D.g₂ (T.ix c n) (T.ix (c + 1) n) i := by
  unfold cphase
  rw [if_neg (by omega), if_pos (by omega), show 4 + i - 4 = i by omega]

/-! ### Evaluation inside the first free gadget -/

lemma xphase_c1_odd (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (7 + 2 * p) = D.comp1 c (T.ix c n) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (7 + 2 * p - 7) / 2 = p by omega]

lemma xphase_c1_even (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (8 + 2 * p) = D.comp1 c (T.ix c n) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (8 + 2 * p - 7) / 2 = p by omega]

lemma xphase_e1_odd (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (7 + 2 * D.P + 2 * p) = D.exp1 c (T.jx c n) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (7 + 2 * D.P + 2 * p - 7 - 2 * D.P) / 2 = p by omega]

lemma xphase_e1_even (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (8 + 2 * D.P + 2 * p) = D.exp1 c (T.jx c n) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (8 + 2 * D.P + 2 * p - 7 - 2 * D.P) / 2 = p by omega]

lemma cphase_free1 (c n : ℤ) (j : ℕ) (h1 : 9 ≤ j) (h2 : j ≤ 8 + 4 * D.P) :
    T.cphase c n j = 0 := by
  unfold cphase
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-! ### Evaluation inside the last two matching gadgets -/

lemma xphase_m3 (c n : ℤ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ 4) :
    T.xphase c n (8 + 4 * D.P + i) = D.mxv D.g₃ (T.jx c n) i := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show 8 + 4 * D.P + i - 8 - 4 * D.P = i by omega]

lemma cphase_m3 (c n : ℤ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ 4) :
    T.cphase c n (8 + 4 * D.P + i) = mcorr D.g₃ (T.jx c n) (T.jx (c + 1) n) i := by
  unfold cphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 8 + 4 * D.P + i - 8 - 4 * D.P = i by omega]

lemma xphase_m4 (c n : ℤ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ 4) :
    T.xphase c n (12 + 4 * D.P + i) = D.mxv D.g₄ (T.jx c n) i := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega),
    show 12 + 4 * D.P + i - 12 - 4 * D.P = i by omega]

lemma cphase_m4 (c n : ℤ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ 4) :
    T.cphase c n (12 + 4 * D.P + i) = mcorr D.g₄ (T.jx c n) (T.jx (c + 1) n) i := by
  unfold cphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show 12 + 4 * D.P + i - 12 - 4 * D.P = i by omega]

/-! ### Evaluation inside the second free gadget -/

lemma xphase_c2_odd (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (15 + 4 * D.P + 2 * p) = D.comp2 c (T.jx c n) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (15 + 4 * D.P + 2 * p - 15 - 4 * D.P) / 2 = p by omega]

lemma xphase_c2_even (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (16 + 4 * D.P + 2 * p) = D.comp2 c (T.jx c n) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (16 + 4 * D.P + 2 * p - 15 - 4 * D.P) / 2 = p by omega]

lemma xphase_e2_odd (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (15 + 6 * D.P + 2 * p) = D.exp2 c (T.ix c (n + 1)) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show (15 + 6 * D.P + 2 * p - 15 - 6 * D.P) / 2 = p by omega]

lemma xphase_e2_even (c n : ℤ) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ D.P) :
    T.xphase c n (16 + 6 * D.P + 2 * p) = D.exp2 c (T.ix c (n + 1)) (p : ℤ) := by
  unfold xphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show (16 + 6 * D.P + 2 * p - 15 - 6 * D.P) / 2 = p by omega]

lemma cphase_free2 (c n : ℤ) (j : ℕ) (h1 : 17 + 4 * D.P ≤ j) : T.cphase c n j = 0 := by
  unfold cphase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-! ### The wrap-around at the end of a cycle -/

lemma xphase_wrap (c n : ℤ) : T.xphase c n D.sN = T.xphase c (n + 1) 0 := by
  have hp : 1 ≤ D.P := by unfold ABData.P; omega
  have hsN : D.sN = 16 + 6 * D.P + 2 * D.P := by unfold ABData.sN; omega
  rw [hsN, T.xphase_e2_even c n D.P hp (le_refl _), T.xphase_m1 c (n + 1) 0 (by omega)]
  rw [D.pz_cast, D.exp2_top (T.ix_one_le c (n + 1))]
  unfold ABData.mxv
  norm_num

lemma cphase_wrap (c n : ℤ) : T.cphase c n D.sN = T.cphase c (n + 1) 0 := by
  have hp : 1 ≤ D.P := by unfold ABData.P; omega
  have hsN : D.sN = 16 + 8 * D.P := rfl
  rw [T.cphase_free2 c n D.sN (by omega), T.cphase_m1 c (n + 1) 0 (by omega)]
  unfold mcorr
  norm_num

lemma yphase_wrap (c n : ℤ) : T.yphase c n D.sN = T.yphase c (n + 1) 0 := by
  unfold yphase
  rw [T.xphase_wrap, T.cphase_wrap]

end IndexTiling

end ABSim

end StickPolyhex
