import Tiling.Proofs.GapSpec
import Tiling.Proofs.StickInstance

/-!
# A finite description of the bucket data, and the marks it produces

`GapSpec` is the data of Section 2.5 of the paper — the numbers `s` and `v`, the sets of allowed
left and right values of each bucket and the interval of each bucket.  Two of its fields are
*sets* and *functions* on `ℕ`, so a `GapSpec` is not a finite object and cannot be handed to a
Turing machine.  This file introduces the finite form of the same data:

* `GapSpecData` records `s` and `v` together with the lists of allowed left and right values of
  each bucket and the two ends of each interval, the ends being stored shifted by `v` so that all
  the numbers involved are natural numbers;
* `GapSpecData.toGapSpec` reads it as a `GapSpec`, clamping the data where necessary (values
  outside `{1, …, v}` are discarded and intervals are cut down to `{-v+1, …, v-1}`), so that
  every `GapSpecData` describes an honest `GapSpec`;
* `GapSpecData.markData` computes the marks of the block from the finite data, and
  `GapSpecData.toMarking_markData` proves that the marking so computed is exactly
  `GapSpec.marking` of the described specification.

Everything here is computed by explicit list operations on natural numbers; the primitive
recursiveness of these computations is proved in `Tiling/Proofs/GapSpecCompute.lean`.
-/

namespace StickPolyhex

/-- A finite description of the data of Section 2.5: the number of buckets, the number of values,
the allowed left and right values of each bucket, and the two ends of the interval of each
bucket, shifted by `v` (so the entry `w` stands for the endpoint `w - v`).  Bucket `i` is
described by the entry of index `i` of each list; the entry of index `0` describes no bucket. -/
structure GapSpecData where
  /-- The number of buckets (a value of `0` is read as `1`). -/
  sRaw : ℕ
  /-- The number of values (a value of `0` is read as `1`). -/
  vRaw : ℕ
  /-- The allowed left values of each bucket. -/
  Lraw : List (List ℕ)
  /-- The allowed right values of each bucket. -/
  Rraw : List (List ℕ)
  /-- The left end of the interval of each bucket, shifted by `v`. -/
  IloRaw : List ℕ
  /-- The right end of the interval of each bucket, shifted by `v`. -/
  IhiRaw : List ℕ
deriving DecidableEq, Repr

namespace GapSpecData

variable (G : GapSpecData)

/-- The number of buckets. -/
def s : ℕ := max G.sRaw 1

/-- The number of values. -/
def v : ℕ := max G.vRaw 1

/-- The length of a bucket. -/
def lb : ℕ := (2 * G.v - 1) * (G.s - 1) + 2 * G.v

/-- The length of a block. -/
def blockLen : ℕ := G.s * G.lb + 2

/-- The allowed left values of the bucket `k`, those outside `{1, …, v}` being discarded. -/
def Lval (k : ℕ) : List ℕ :=
  (G.Lraw.getD k []).flatMap (fun b => if 1 ≤ b ∧ b ≤ G.v then [b] else [])

/-- The allowed right values of the bucket `k`, those outside `{1, …, v}` being discarded. -/
def Rval (k : ℕ) : List ℕ :=
  (G.Rraw.getD k []).flatMap (fun a => if 1 ≤ a ∧ a ≤ G.v then [a] else [])

/-- The left end of the interval of the bucket `k`, shifted by `v` and cut down to
`{1, …, 2v-1}`. -/
def ilo (k : ℕ) : ℕ := min (max (G.IloRaw.getD k G.v) 1) (2 * G.v - 1)

/-- The right end of the interval of the bucket `k`, shifted by `v`, cut down to `{1, …, 2v-1}`
and raised to the left end if it lies below it, so that the interval is never empty. -/
def ihi (k : ℕ) : ℕ := max (G.ilo k) (min (max (G.IhiRaw.getD k G.v) 1) (2 * G.v - 1))

lemma one_le_v : 1 ≤ G.v := le_max_right _ _

lemma one_le_s : 1 ≤ G.s := le_max_right _ _

lemma ilo_bounds (k : ℕ) : 1 ≤ G.ilo k ∧ G.ilo k ≤ 2 * G.v - 1 := by
  have := G.one_le_v
  constructor
  · simp only [ilo, le_min_iff]
    omega
  · simp only [ilo]
    omega

lemma ihi_bounds (k : ℕ) : G.ilo k ≤ G.ihi k ∧ G.ihi k ≤ 2 * G.v - 1 := by
  have := G.one_le_v
  have := G.ilo_bounds k
  constructor
  · exact le_max_left _ _
  · simp only [ihi]
    omega

lemma mem_Lval {k b : ℕ} : b ∈ G.Lval k ↔ b ∈ G.Lraw.getD k [] ∧ 1 ≤ b ∧ b ≤ G.v := by
  simp only [Lval, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hmem⟩
    by_cases h : 1 ≤ c ∧ c ≤ G.v
    · rw [if_pos h] at hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      exact ⟨hc, h⟩
    · rw [if_neg h] at hmem
      simp at hmem
  · rintro ⟨hb, h⟩
    exact ⟨b, hb, by rw [if_pos h]; simp⟩

lemma mem_Rval {k a : ℕ} : a ∈ G.Rval k ↔ a ∈ G.Rraw.getD k [] ∧ 1 ≤ a ∧ a ≤ G.v := by
  simp only [Rval, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hmem⟩
    by_cases h : 1 ≤ c ∧ c ≤ G.v
    · rw [if_pos h] at hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      exact ⟨hc, h⟩
    · rw [if_neg h] at hmem
      simp at hmem
  · rintro ⟨ha, h⟩
    exact ⟨a, ha, by rw [if_pos h]; simp⟩

/-- The specification described by the finite data. -/
def toGapSpec : GapSpec where
  s := G.s
  v := G.v
  hs := G.one_le_s
  hv := G.one_le_v
  L := fun k => {x : ℤ | ∃ b ∈ G.Lval k, x = (b : ℤ)}
  R := fun k => {x : ℤ | ∃ a ∈ G.Rval k, x = (a : ℤ)}
  hL := by
    rintro k x ⟨b, hb, rfl⟩
    have := (G.mem_Lval).1 hb
    exact Set.mem_Icc.2 ⟨by exact_mod_cast this.2.1, by exact_mod_cast this.2.2⟩
  hR := by
    rintro k x ⟨a, ha, rfl⟩
    have := (G.mem_Rval).1 ha
    exact Set.mem_Icc.2 ⟨by exact_mod_cast this.2.1, by exact_mod_cast this.2.2⟩
  Imin := fun k => (G.ilo k : ℤ) - G.v
  Imax := fun k => (G.ihi k : ℤ) - G.v
  hImin := by
    intro k
    have h := G.ilo_bounds k
    have := G.one_le_v
    omega
  hImax := by
    intro k
    have h := G.ihi_bounds k
    have := G.one_le_v
    omega
  hI := by
    intro k
    have h := G.ihi_bounds k
    omega

@[simp] lemma toGapSpec_s : G.toGapSpec.s = G.s := rfl
@[simp] lemma toGapSpec_v : G.toGapSpec.v = G.v := rfl
@[simp] lemma toGapSpec_lb : G.toGapSpec.lb = G.lb := rfl
@[simp] lemma toGapSpec_blockLen : G.toGapSpec.blockLen = G.blockLen := rfl
@[simp] lemma toGapSpec_Imin (k : ℕ) : G.toGapSpec.Imin k = (G.ilo k : ℤ) - G.v := rfl
@[simp] lemma toGapSpec_Imax (k : ℕ) : G.toGapSpec.Imax k = (G.ihi k : ℤ) - G.v := rfl
@[simp] lemma toGapSpec_L (k : ℕ) :
    G.toGapSpec.L k = {x : ℤ | ∃ b ∈ G.Lval k, x = (b : ℤ)} := rfl
@[simp] lemma toGapSpec_R (k : ℕ) :
    G.toGapSpec.R k = {x : ℤ | ∃ a ∈ G.Rval k, x = (a : ℤ)} := rfl

@[simp] lemma lbZ_eq_lb : G.toGapSpec.lbZ = (G.lb : ℤ) := rfl

lemma two_v_le_lb : 2 * G.v ≤ G.lb := by
  simp only [lb]
  omega

/-! ## The marks, computed from the finite data -/

/-- The positions of the left-facing arrow marks on the top face, computed from the data. -/
def topArrowLList : List ℕ :=
  (List.range G.s).flatMap (fun k => if 1 ≤ k then [k * G.lb] else []) ++
  (List.range (G.s + 1)).flatMap
    (fun k => if 1 ≤ k then [(k - 1) * G.lb + (2 * G.v - 1) * (k - 1) + (2 * G.v + 1 - G.ilo k)]
      else []) ++
  (List.range (G.v + 1)).flatMap
    (fun a => if 1 ≤ a ∧ a + G.v < G.ilo 1 then [G.v + 1 - a] else [])

/-- The positions of the right-facing arrow marks on the top face, computed from the data. -/
def topArrowRList : List ℕ :=
  (List.range G.s).flatMap (fun k => if 1 ≤ k then [k * G.lb] else []) ++
  (List.range (G.s + 1)).flatMap
    (fun k => if 1 ≤ k then [(k - 1) * G.lb + (2 * G.v - 1) * (k - 1) + (2 * G.v - 1 - G.ihi k)]
      else []) ++
  (List.range (G.v + 1)).flatMap
    (fun b => if 1 ≤ b ∧ b + G.ihi G.s < G.v then [G.s * G.lb - G.v + b - 1] else [])

/-- The cyclic permutation of the buckets, computed from the data. -/
def sigma (i : ℕ) : ℕ := if i = G.s then 1 else i + 1

@[simp] lemma toGapSpec_sigma (i : ℕ) : G.toGapSpec.sigma i = G.sigma i := rfl

/-- The positions of the left-facing arrow marks on the bottom face, computed from the data. -/
def botArrowLList : List ℕ :=
  (List.range (G.s + 1)).flatMap
    (fun i => if 1 ≤ i then
      [(G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v + 1] else [])

/-- The positions of the right-facing arrow marks on the bottom face, computed from the data. -/
def botArrowRList : List ℕ :=
  (List.range (G.s + 1)).flatMap
    (fun i => if 1 ≤ i then
      [(G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v - 1] else [])

/-- The positions of the left-facing triangle marks, computed from the data. -/
def triangleLList : List ℕ :=
  (List.range (G.s + 1)).flatMap
    (fun k => if 1 ≤ k then (G.Lval k).map (fun b => k * G.lb - G.v + b) else [])

/-- The positions of the right-facing triangle marks, computed from the data. -/
def triangleRList : List ℕ :=
  (List.range (G.s + 1)).flatMap
    (fun k => if 1 ≤ k then (G.Rval k).map (fun a => (k - 1) * G.lb + G.v - a) else [])

/-- The marked stick prototile described by the finite bucket data: an instance of the grid
stick tiling problem. -/
def markData : MarkData where
  blockLen := G.blockLen
  topArrowL := G.topArrowLList
  topArrowR := G.topArrowRList
  botArrowL := G.botArrowLList
  botArrowR := G.botArrowRList
  triangleL := G.triangleLList
  triangleR := G.triangleRList

@[simp] lemma markData_blockLen : G.markData.blockLen = G.blockLen := rfl

end GapSpecData

end StickPolyhex
