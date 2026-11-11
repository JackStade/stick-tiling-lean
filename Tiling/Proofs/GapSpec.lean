import Tiling.Proofs.Markings
import Tiling.Proofs.GapGeometry

/-!
# Buckets, values and the markings they produce

This file carries out the construction of Section 2.5 of the paper: given the numbers `s` (the
number of buckets) and `v` (the number of values), and, for each bucket `1 ≤ i ≤ s`, the sets
`L i`, `R i ⊆ {1, …, v}` of allowed left and right values and the interval
`I i = [Imin i, Imax i] ⊆ {-v+1, …, v-1}`, it fixes the length of a block and places the arrow
and triangle marks on it.

## The layout of a block

The block is divided into `s` *buckets*, each of length `lb = (2v-1)(s-1) + 2v`, and carries two
extra unit segments, one at each end; so a block has length `blockLen = s * lb + 2`.  The bucket
`i` occupies the positions `(i-1) * lb, …, i * lb` of the block (recall that the position `p` is
the boundary between the columns `p` and `p + 1` of the block, so that a block of length `N` has
the positions `0, …, N - 1`).

## The marks

* **Triangles.**  A right-facing triangle is placed at the position `(i-1) * lb + v - a` for each
  bucket `i` and each allowed right value `a ∈ R i`, and a left-facing triangle at the position
  `i * lb - v + b` for each allowed left value `b ∈ L i`.  Right-facing triangles therefore only
  occur in the left half of a bucket and left-facing ones only in the right half.
* **Arrows on the top face.**  At each boundary `i * lb` between two buckets there is a pair of
  arrows facing back to back (in the present encoding both of them sit at the boundary position
  itself); they prevent a gap from crossing the boundary.  Inside the bucket `i` there is a pair
  of arrows facing each other, a right-facing one at
  `(i-1) * lb + (2v-1)(i-1) + v - 1 - Imax i` and a left-facing one at
  `(i-1) * lb + (2v-1)(i-1) + v + 1 - Imin i`; they force the change of direction of a gap lying
  above the bucket `i` to happen in the range prescribed by the interval `I i`.
  Finally, whenever the interval `I 1` (resp. `I s`) is so far from `0` that some values are
  incompatible with *every* gap, extra arrows are placed which forbid those configurations
  outright; these are the third alternative in the definitions of `topArrowL` and `topArrowR`
  below.  (The arrows of the paper cannot do this by themselves: an arrow only constrains a gap
  that lies above it.)
* **Arrows on the bottom face.**  Below the bucket `s - i + 1` there is a pair of arrows facing
  the relative position `(2v-1)(σ i - 1) + v`, encoded here as a right-facing arrow at
  `(s-i) * lb + (2v-1)(σ i - 1) + v - 1` and a left-facing one two positions further to the
  right.  They pin down the length of the left part of the gap below the block.
-/

namespace StickPolyhex

/-- The data of Section 2.5 of the paper: the number `s` of buckets, the number `v` of values,
the sets `L i`, `R i ⊆ {1, …, v}` of left and right values allowed in the bucket `i`, and the
interval `I i = [Imin i, Imax i] ⊆ {-v+1, …, v-1}` bounding the difference of the values of
gaps in adjacent rows. -/
structure GapSpec where
  /-- The number of buckets. -/
  s : ℕ
  /-- The number of values. -/
  v : ℕ
  /-- There is at least one bucket. -/
  hs : 1 ≤ s
  /-- There is at least one value. -/
  hv : 1 ≤ v
  /-- The left values allowed in each bucket. -/
  L : ℕ → Set ℤ
  /-- The right values allowed in each bucket. -/
  R : ℕ → Set ℤ
  /-- Left values lie in `{1, …, v}`. -/
  hL : ∀ i, L i ⊆ Set.Icc 1 (v : ℤ)
  /-- Right values lie in `{1, …, v}`. -/
  hR : ∀ i, R i ⊆ Set.Icc 1 (v : ℤ)
  /-- The left end of the interval of the bucket `i`. -/
  Imin : ℕ → ℤ
  /-- The right end of the interval of the bucket `i`. -/
  Imax : ℕ → ℤ
  /-- The interval of each bucket is contained in `{-v+1, …, v-1}`. -/
  hImin : ∀ i, -(v : ℤ) + 1 ≤ Imin i
  /-- The interval of each bucket is contained in `{-v+1, …, v-1}`. -/
  hImax : ∀ i, Imax i ≤ (v : ℤ) - 1
  /-- The interval of each bucket is non-empty. -/
  hI : ∀ i, Imin i ≤ Imax i

namespace GapSpec

variable (G : GapSpec)

/-- The length of a bucket. -/
def lb : ℕ := (2 * G.v - 1) * (G.s - 1) + 2 * G.v

/-- The length of a block: `s` buckets and one extra unit segment at each end. -/
def blockLen : ℕ := G.s * G.lb + 2

/-- The cyclic permutation of the states: `σ i = i + 1`, and `σ s = 1`. -/
def sigma (i : ℕ) : ℕ := if i = G.s then 1 else i + 1

/-- The length of a bucket, as an integer. -/
def lbZ : ℤ := (G.lb : ℤ)

lemma lbZ_eq : G.lbZ = (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) + 2 * G.v := by
  have hv := G.hv
  have hs := G.hs
  unfold lbZ lb
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * G.v), Nat.cast_sub hs]
  ring

lemma two_v_le_lbZ : 2 * (G.v : ℤ) ≤ G.lbZ := by
  have hv := G.hv
  have hs := G.hs
  rw [G.lbZ_eq]
  have h1 : (0 : ℤ) ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) := by
    apply mul_nonneg <;> omega
  omega

lemma blockLenZ : (G.blockLen : ℤ) = (G.s : ℤ) * G.lbZ + 2 := by
  unfold blockLen lbZ; push_cast; ring

lemma sigma_mem {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ G.s) : 1 ≤ G.sigma i ∧ G.sigma i ≤ G.s := by
  unfold sigma
  split <;> omega

/-- The marks placed on a block by the construction of Section 2.5. -/
def marking : Marking G.blockLen where
  topArrowL := {p : ℕ |
    (∃ k : ℕ, 1 ≤ k ∧ k < G.s ∧ (p : ℤ) = (k : ℤ) * G.lbZ) ∨
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧
      (p : ℤ) = ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v + 1
        - G.Imin k) ∨
    (∃ a : ℤ, 1 ≤ a ∧ a ≤ (G.v : ℤ) ∧ a < G.Imin 1 ∧ (p : ℤ) = (G.v : ℤ) + 1 - a)}
  topArrowR := {p : ℕ |
    (∃ k : ℕ, 1 ≤ k ∧ k < G.s ∧ (p : ℤ) = (k : ℤ) * G.lbZ) ∨
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧
      (p : ℤ) = ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v - 1
        - G.Imax k) ∨
    (∃ b : ℤ, 1 ≤ b ∧ b ≤ (G.v : ℤ) ∧ b < - G.Imax G.s ∧
      (p : ℤ) = (G.s : ℤ) * G.lbZ - G.v + b - 1)}
  botArrowL := {p : ℕ | ∃ i : ℕ, 1 ≤ i ∧ i ≤ G.s ∧
    (p : ℤ) = ((G.s : ℤ) - i) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) + G.v + 1}
  botArrowR := {p : ℕ | ∃ i : ℕ, 1 ≤ i ∧ i ≤ G.s ∧
    (p : ℤ) = ((G.s : ℤ) - i) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) + G.v - 1}
  triangleL := {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧ ∃ b ∈ G.L k,
    (p : ℤ) = (k : ℤ) * G.lbZ - G.v + b}
  triangleR := {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧ ∃ a ∈ G.R k,
    (p : ℤ) = ((k : ℤ) - 1) * G.lbZ + G.v - a}

@[simp] lemma mem_triangleR {p : ℕ} : p ∈ G.marking.triangleR ↔
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧ ∃ a ∈ G.R k, (p : ℤ) = ((k : ℤ) - 1) * G.lbZ + G.v - a := Iff.rfl

@[simp] lemma mem_triangleL {p : ℕ} : p ∈ G.marking.triangleL ↔
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧ ∃ b ∈ G.L k, (p : ℤ) = (k : ℤ) * G.lbZ - G.v + b := Iff.rfl

@[simp] lemma mem_botArrowL {p : ℕ} : p ∈ G.marking.botArrowL ↔
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ G.s ∧
      (p : ℤ) = ((G.s : ℤ) - i) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) + G.v + 1 :=
  Iff.rfl

@[simp] lemma mem_botArrowR {p : ℕ} : p ∈ G.marking.botArrowR ↔
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ G.s ∧
      (p : ℤ) = ((G.s : ℤ) - i) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) + G.v - 1 :=
  Iff.rfl

@[simp] lemma mem_topArrowL {p : ℕ} : p ∈ G.marking.topArrowL ↔
    ((∃ k : ℕ, 1 ≤ k ∧ k < G.s ∧ (p : ℤ) = (k : ℤ) * G.lbZ) ∨
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧
      (p : ℤ) = ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v + 1
        - G.Imin k) ∨
    (∃ a : ℤ, 1 ≤ a ∧ a ≤ (G.v : ℤ) ∧ a < G.Imin 1 ∧ (p : ℤ) = (G.v : ℤ) + 1 - a)) := Iff.rfl

@[simp] lemma mem_topArrowR {p : ℕ} : p ∈ G.marking.topArrowR ↔
    ((∃ k : ℕ, 1 ≤ k ∧ k < G.s ∧ (p : ℤ) = (k : ℤ) * G.lbZ) ∨
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧
      (p : ℤ) = ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v - 1
        - G.Imax k) ∨
    (∃ b : ℤ, 1 ≤ b ∧ b ≤ (G.v : ℤ) ∧ b < - G.Imax G.s ∧
      (p : ℤ) = (G.s : ℤ) * G.lbZ - G.v + b - 1)) := Iff.rfl

end GapSpec

end StickPolyhex
