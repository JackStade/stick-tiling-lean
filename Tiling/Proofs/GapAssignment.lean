import Tiling.Proofs.GapMain

/-!
# Abstract gap data, and the layout it prescribes

The gap conditions of Section 2.5 of the paper (`Schematic.GapConditions`) are conditions on a
schematic.  This file, together with `Tiling/Proofs/GapSchematic.lean`, goes the other way
round: it starts from the *combinatorial* data of a state for every row and of a pair of values
for every gap, subject to the paper's conditions, and builds a schematic realising them.

## The data

`GapAssignment G` records

* a state `st r ∈ {1, …, s}` for every row `r`, with `st (r - 1) = σ (st r)`;
* the two values `xv r k ∈ L (st r)` and `yv r k ∈ R (st r)` of the `k`-th gap of the row `r`,
  the gaps of each row being indexed by `ℤ` from left to right in such a way that the `k`-th gap
  of the row `r` lies above the block of the row `r - 1` bounded by the gaps `k` and `k + 1`;
* the paper's two remaining conditions: `x + y = x' + y'` (`value_sum`), where `x'` is the right
  value of the gap below to the left and `y'` the left value of the gap below to the right, and
  `x' - x ∈ I (st (r-1))` (`interval`).

## The layout

All the positions of the schematic are then forced, up to one global horizontal translation per
connected piece of information — in fact up to a single global translation, since the relative
offset of two adjacent rows is determined by the values.  Writing `l` and `m` for the lengths of
the two parts of a gap and `j` for the block column above which it starts,

* `lenLz r k = (2v-1)(st (r-1) - 1) + x r k` and `lenRz r k = (2v-1)(s - st (r-1)) + y r k`
  are the two lengths (so that the values of the gap are exactly `x r k` and `y r k`);
* `offz r k = 2 + (st (r-1) - 1) lb + v - y (r-1) k` is the block column above which the gap
  starts, as prescribed by the alignment condition `align_left`;
* `gapStart r k` is the column of the schematic at which the `k`-th gap of the row `r` starts;
  it is defined by summing the above data, and `gapStart_shift` records that the offset between
  two adjacent rows is the prescribed one.

The main arithmetic facts proved here are `two_le_offz` and `offz_add_lenz_le`, which say that
the gap fits strictly inside the block below it (this is where `value_sum` is used), and
`gapStart_shift`.
-/

namespace StickPolyhex

/-- The sum of `f i` for `i` running from `0` to `k`, defined for `k` of either sign so that
`zsum f 0 = 0` and `zsum f (k + 1) = zsum f k + f k`. -/
noncomputable def zsum (f : ℤ → ℤ) (k : ℤ) : ℤ :=
  if 0 ≤ k then ∑ i ∈ Finset.range k.toNat, f i
  else -∑ i ∈ Finset.range (-k).toNat, f (-(i : ℤ) - 1)

@[simp] lemma zsum_zero (f : ℤ → ℤ) : zsum f 0 = 0 := by simp [zsum]

lemma zsum_succ (f : ℤ → ℤ) (k : ℤ) : zsum f (k + 1) = zsum f k + f k := by
  rcases le_or_gt 0 k with hk | hk
  · rw [zsum, zsum, if_pos (by omega), if_pos hk,
      show (k + 1).toNat = k.toNat + 1 by omega, Finset.sum_range_succ]
    congr 2
    omega
  · rcases eq_or_lt_of_le (show k + 1 ≤ 0 by omega) with h0 | h0
    · rw [show k = -1 by omega]
      norm_num [zsum]
    · rw [zsum, zsum, if_neg (by omega), if_neg (by omega),
        show (-k).toNat = (-(k + 1)).toNat + 1 by omega, Finset.sum_range_succ,
        show (-((((-(k + 1)).toNat : ℕ)) : ℤ) - 1) = k by omega]
      ring

/-- The combinatorial data the gap conditions of Section 2.5 of the paper talk about: a state for
every row, and a pair of values for every gap, subject to the paper's conditions.  The gaps of
each row are indexed by `ℤ` from left to right, the `k`-th gap of the row `r` lying above the
block of the row `r - 1` bounded by the gaps `k` (on its left) and `k + 1` (on its right). -/
structure GapAssignment (G : GapSpec) where
  /-- The state of a row: the bucket of its blocks above which the gaps of the row above lie. -/
  st : ℤ → ℕ
  /-- The left value of the `k`-th gap of the row `r`. -/
  xv : ℤ → ℤ → ℤ
  /-- The right value of the `k`-th gap of the row `r`. -/
  yv : ℤ → ℤ → ℤ
  /-- Every state is one of the `s` buckets. -/
  state_mem : ∀ r, 1 ≤ st r ∧ st r ≤ G.s
  /-- The row below a row of state `i` has state `σ i`. -/
  state_cycle : ∀ r, st (r - 1) = G.sigma (st r)
  /-- The left value of a gap of a row of state `i` lies in `L i`. -/
  x_mem : ∀ r k, xv r k ∈ G.L (st r)
  /-- The right value of a gap of a row of state `i` lies in `R i`. -/
  y_mem : ∀ r k, yv r k ∈ G.R (st r)
  /-- The paper's condition `x + y = x' + y'`. -/
  value_sum : ∀ r k, xv r k + yv r k = yv (r - 1) k + xv (r - 1) (k + 1)
  /-- The paper's condition `x' - x ∈ I`. -/
  interval : ∀ r k, G.Imin (st (r - 1)) ≤ yv (r - 1) k - xv r k ∧
    yv (r - 1) k - xv r k ≤ G.Imax (st (r - 1))

namespace GapAssignment

variable {G : GapSpec} (A : GapAssignment G)

/-! ### Elementary bounds -/

lemma one_le_st (r : ℤ) : 1 ≤ A.st r := (A.state_mem r).1

lemma st_le (r : ℤ) : A.st r ≤ G.s := (A.state_mem r).2

lemma one_le_xv (r k : ℤ) : 1 ≤ A.xv r k := (G.hL _ (A.x_mem r k)).1

lemma xv_le (r k : ℤ) : A.xv r k ≤ (G.v : ℤ) := (G.hL _ (A.x_mem r k)).2

lemma one_le_yv (r k : ℤ) : 1 ≤ A.yv r k := (G.hR _ (A.y_mem r k)).1

lemma yv_le (r k : ℤ) : A.yv r k ≤ (G.v : ℤ) := (G.hR _ (A.y_mem r k)).2

lemma value_sum' (r k : ℤ) : A.xv (r + 1) k + A.yv (r + 1) k = A.yv r k + A.xv r (k + 1) := by
  have := A.value_sum (r + 1) k
  simpa using this

/-! ### The lengths and offsets prescribed by the data -/

/-- The length of the left part of the `k`-th gap of the row `r`. -/
def lenLz (r k : ℤ) : ℤ := (2 * (G.v : ℤ) - 1) * ((A.st (r - 1) : ℤ) - 1) + A.xv r k

/-- The length of the right part of the `k`-th gap of the row `r`. -/
def lenRz (r k : ℤ) : ℤ := (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (A.st (r - 1) : ℤ)) + A.yv r k

/-- The total length of the `k`-th gap of the row `r`. -/
def lenz (r k : ℤ) : ℤ := A.lenLz r k + A.lenRz r k

/-- The column of the block of the row `r - 1` above which the `k`-th gap of the row `r`
starts. -/
def offz (r k : ℤ) : ℤ :=
  2 + ((A.st (r - 1) : ℤ) - 1) * G.lbZ + (G.v : ℤ) - A.yv (r - 1) k

lemma one_le_lenLz (r k : ℤ) : 1 ≤ A.lenLz r k := by
  have h1 : (0 : ℤ) ≤ (2 * (G.v : ℤ) - 1) * ((A.st (r - 1) : ℤ) - 1) := by
    have := A.one_le_st (r - 1)
    have := G.hv
    apply mul_nonneg <;> omega
  have := A.one_le_xv r k
  unfold lenLz
  omega

lemma one_le_lenRz (r k : ℤ) : 1 ≤ A.lenRz r k := by
  have h1 : (0 : ℤ) ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (A.st (r - 1) : ℤ)) := by
    have := A.st_le (r - 1)
    have := G.hv
    apply mul_nonneg <;> omega
  have := A.one_le_yv r k
  unfold lenRz
  omega

lemma two_le_lenz (r k : ℤ) : 2 ≤ A.lenz r k := by
  have := A.one_le_lenLz r k
  have := A.one_le_lenRz r k
  unfold lenz
  omega

/-- The total length of a gap depends only on its two values. -/
lemma lenz_eq (r k : ℤ) :
    A.lenz r k = (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) + A.xv r k + A.yv r k := by
  unfold lenz lenLz lenRz
  ring

/-- A gap starts at least two columns to the right of the left end of the block below it. -/
lemma two_le_offz (r k : ℤ) : 2 ≤ A.offz r k := by
  have h1 : (0 : ℤ) ≤ ((A.st (r - 1) : ℤ) - 1) * G.lbZ := by
    have := A.one_le_st (r - 1)
    have := G.two_v_le_lbZ
    have := G.hv
    apply mul_nonneg <;> omega
  have := A.yv_le (r - 1) k
  unfold offz
  omega

/-- A gap ends at least one column to the left of the right end of the block below it: this is
where the paper's condition `x + y = x' + y'` is used. -/
lemma offz_add_lenz_le (r k : ℤ) : A.offz r k + A.lenz r k ≤ (G.blockLen : ℤ) := by
  have hsum := A.value_sum r k
  have hlen := A.lenz_eq r k
  have hlb := G.lbZ_eq
  have hx := A.xv_le (r - 1) (k + 1)
  have hi : (A.st (r - 1) : ℤ) ≤ (G.s : ℤ) := by exact_mod_cast A.st_le (r - 1)
  have h1 : (0 : ℤ) ≤ ((G.s : ℤ) - (A.st (r - 1) : ℤ)) * G.lbZ := by
    have := G.two_v_le_lbZ
    have := G.hv
    apply mul_nonneg <;> omega
  have hblock := G.blockLenZ
  unfold offz
  nlinarith [hlen, hsum, h1, hblock, hlb]

/-! ### The positions -/

/-- The column at which the `0`-th gap of the row `r` starts (the global horizontal offset being
normalised so that the `0`-th gap of the row `0` starts at the column `0`). -/
noncomputable def rowBase (r : ℤ) : ℤ := zsum (fun t => A.lenz t 0 + A.offz (t + 1) 0) r

/-- The column at which the `k`-th gap of the row `r` starts. -/
noncomputable def gapStart (r k : ℤ) : ℤ :=
  A.rowBase r + zsum (fun i => A.lenz r i + (G.blockLen : ℤ) + 1) k

/-- The column at which the block following the `k`-th gap of the row `r` starts. -/
noncomputable def gapEnd (r k : ℤ) : ℤ := A.gapStart r k + A.lenz r k

lemma gapStart_succ (r k : ℤ) :
    A.gapStart r (k + 1) = A.gapEnd r k + (G.blockLen : ℤ) + 1 := by
  simp only [gapStart, gapEnd, zsum_succ]
  ring

lemma gapStart_lt_gapEnd (r k : ℤ) : A.gapStart r k < A.gapEnd r k := by
  have := A.two_le_lenz r k
  unfold gapEnd
  omega

lemma gapEnd_lt_gapStart_succ (r k : ℤ) : A.gapEnd r k < A.gapStart r (k + 1) := by
  have := G.blockLenZ
  have := G.two_v_le_lbZ
  have := G.hv
  have := G.hs
  have h : (0 : ℤ) ≤ (G.s : ℤ) * G.lbZ := by
    apply mul_nonneg <;> [exact_mod_cast Nat.zero_le _; omega]
  rw [A.gapStart_succ]
  omega

lemma gapStart_lt_succ (r k : ℤ) : A.gapStart r k < A.gapStart r (k + 1) :=
  lt_trans (A.gapStart_lt_gapEnd r k) (A.gapEnd_lt_gapStart_succ r k)

lemma gapStart_strictMono (r : ℤ) : StrictMono (A.gapStart r) :=
  strictMono_int_of_lt_succ (A.gapStart_lt_succ r)

lemma gapEnd_strictMono (r : ℤ) : StrictMono (A.gapEnd r) := by
  refine strictMono_int_of_lt_succ (fun k => ?_)
  exact lt_trans (A.gapEnd_lt_gapStart_succ r k) (A.gapStart_lt_gapEnd r (k + 1))

/-- **The relative offset of two adjacent rows is determined by the values**: the `k`-th gap of
the row `r + 1` starts exactly `offz (r+1) k` columns after the beginning of the block of the row
`r` that follows the `k`-th gap of that row. -/
lemma gapStart_shift (r k : ℤ) :
    A.gapStart (r + 1) k = A.gapEnd r k + A.offz (r + 1) k := by
  have hbase : A.rowBase (r + 1) = A.rowBase r + A.lenz r 0 + A.offz (r + 1) 0 := by
    unfold rowBase
    rw [zsum_succ]
    ring
  induction k using Int.induction_on with
  | zero => simp only [gapEnd, gapStart, zsum_zero, add_zero, hbase]
  | succ i ih =>
    have h1 := A.gapStart_succ (r + 1) i
    have h2 := A.gapStart_succ r i
    have hkey : A.offz (r + 1) i + A.lenz (r + 1) i
        = A.lenz r (i + 1) + A.offz (r + 1) (i + 1) := by
      have hs := A.value_sum' r i
      have e1 := A.lenz_eq (r + 1) i
      have e2 := A.lenz_eq r (i + 1)
      unfold offz
      simp only [add_sub_cancel_right]
      omega
    unfold gapEnd at h1 h2 ih ⊢
    omega
  | pred i ih =>
    have h1 := A.gapStart_succ (r + 1) (-(i : ℤ) - 1)
    have h2 := A.gapStart_succ r (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h1 h2
    have hkey : A.offz (r + 1) (-(i : ℤ) - 1) + A.lenz (r + 1) (-(i : ℤ) - 1)
        = A.lenz r (-(i : ℤ)) + A.offz (r + 1) (-(i : ℤ)) := by
      have hs := A.value_sum' r (-(i : ℤ) - 1)
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at hs
      have e1 := A.lenz_eq (r + 1) (-(i : ℤ) - 1)
      have e2 := A.lenz_eq r (-(i : ℤ))
      unfold offz
      simp only [add_sub_cancel_right]
      omega
    unfold gapEnd at h1 h2 ih ⊢
    omega

end GapAssignment

end StickPolyhex
