import Tiling.Proofs.GapArrows

/-!
# Reading the bucket and the values of a gap off the marks

Let `S` be a schematic whose blocks carry the marks `G.marking` of Section 2.5, and let `G'` be
a gap of `S` lying above the columns `j, …, j + l + m - 1` of a block of the row below.  The two
triangle marks below the ends of the gap say that

* `j - 2 = (k-1) * lb + v - a` for some bucket `k` and some `a ∈ R k`, and
* `j + l + m - 2 = k' * lb - v + b` for some bucket `k'` and some `b ∈ L k'`,

and the pair of arrows at the boundary of two buckets forces `k = k'`: the gap lies above a
single bucket.  This is `Schematic.decode` below; `Bucketed` records the resulting data.

The pair of arrows inside the bucket `k` then confines the length `l` of the left part of the
gap to the interval prescribed by `I k` (`Schematic.length_bounds`).
-/

namespace StickPolyhex

namespace GapSpec

variable (G : GapSpec)

lemma lbZ_pos : 0 < G.lbZ := by
  have := G.two_v_le_lbZ
  have := G.hv
  have : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  omega

lemma v_le_lbZ : (G.v : ℤ) ≤ G.lbZ := by
  have := G.two_v_le_lbZ
  have : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  omega

/-- Two decompositions `(k - 1) * lb + c` with `0 ≤ c < lb` agree. -/
lemma bucket_index_eq {k k' : ℕ} {c c' : ℤ} (hc : 0 ≤ c) (hc' : c < G.lbZ) (hd : 0 ≤ c')
    (hd' : c' < G.lbZ) (h : ((k : ℤ) - 1) * G.lbZ + c = ((k' : ℤ) - 1) * G.lbZ + c') :
    k = k' := by
  have hpos := G.lbZ_pos
  have key : ((k : ℤ) - k') * G.lbZ = c' - c := by ring_nf; ring_nf at h; linarith
  have : (k : ℤ) = k' := by
    rcases lt_trichotomy ((k : ℤ) - k') 0 with hlt | heq | hgt
    · exfalso
      have : ((k : ℤ) - k') * G.lbZ ≤ -G.lbZ := by nlinarith
      omega
    · omega
    · exfalso
      have : G.lbZ ≤ ((k : ℤ) - k') * G.lbZ := by nlinarith
      omega
  exact_mod_cast this

end GapSpec

namespace Schematic

variable {G : GapSpec} {S : Schematic G.blockLen}

/-- The data read off the two triangle marks at the ends of a gap: the gap lies above the bucket
`k`, its left end sits at the relative position `v - a` and its right end at the relative
position `lb - v + b` of that bucket, where `a ∈ R k` and `b ∈ L k`. -/
structure Bucketed (G : GapSpec) (l m j k : ℕ) (a b : ℤ) : Prop where
  /-- The bucket index is at least `1`. -/
  k_pos : 1 ≤ k
  /-- The bucket index is at most `s`. -/
  k_le : k ≤ G.s
  /-- The value read at the left end of the gap is allowed. -/
  ha : a ∈ G.R k
  /-- The value read at the right end of the gap is allowed. -/
  hb : b ∈ G.L k
  /-- The position of the left end of the gap. -/
  eL : (j : ℤ) - 2 = ((k : ℤ) - 1) * G.lbZ + G.v - a
  /-- The position of the right end of the gap. -/
  eR : (j : ℤ) + l + m - 2 = (k : ℤ) * G.lbZ - G.v + b

namespace Bucketed

variable {l m j k : ℕ} {a b : ℤ}

lemma a_mem (h : Bucketed G l m j k a b) : 1 ≤ a ∧ a ≤ (G.v : ℤ) := by
  have := G.hR k h.ha; exact ⟨this.1, this.2⟩

lemma b_mem (h : Bucketed G l m j k a b) : 1 ≤ b ∧ b ≤ (G.v : ℤ) := by
  have := G.hL k h.hb; exact ⟨this.1, this.2⟩

/-- The length of a gap in terms of the two values read at its ends. -/
lemma length (h : Bucketed G l m j k a b) : (l : ℤ) + m = G.lbZ - 2 * G.v + a + b := by
  have h1 := h.eL
  have h2 := h.eR
  have : (k : ℤ) * G.lbZ = ((k : ℤ) - 1) * G.lbZ + G.lbZ := by ring
  linarith [h1, h2, this]

end Bucketed

/-- The bucket and the two values of a gap are determined by it. -/
lemma bucketed_unique {l m j k k' : ℕ} {a b a' b' : ℤ} (h : Bucketed G l m j k a b)
    (h' : Bucketed G l m j k' a' b') : k = k' ∧ a = a' ∧ b = b' := by
  have hav := h.a_mem
  have hav' := h'.a_mem
  have hv : (G.v : ℤ) ≤ G.lbZ := G.v_le_lbZ
  have hk : k = k' := by
    refine G.bucket_index_eq (c := (G.v : ℤ) - a) (c' := (G.v : ℤ) - a') (by omega) (by omega)
      (by omega) (by omega) ?_
    have e1 := h.eL
    have e2 := h'.eL
    linarith
  subst hk
  have ha : a = a' := by have := h.eL; have := h'.eL; omega
  subst ha
  have hb : b = b' := by have := h.eR; have := h'.eR; omega
  exact ⟨rfl, rfl, hb⟩

/-- Every gap lies above a single bucket: the paper's first claim in
`Lemma 5` (`lem:gapsinsamebucket`). -/
lemma decode (hM : S.RespectsMarking G.marking) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) : ∃ (k : ℕ) (a b : ℤ), Bucketed G l m j k a b := by
  have hj2 := hg.two_le
  have hl := hg.toGapAt.l_pos
  have hm := hg.toGapAt.m_pos
  obtain ⟨k, hk1, hk2, a, ha, hea⟩ := triangleR_of_gap hM hg
  obtain ⟨k', hk1', hk2', b, hb, heb⟩ := triangleL_of_gap hM hg
  rw [show (((j - 2 : ℕ)) : ℤ) = (j : ℤ) - 2 by omega] at hea
  rw [show (((j + l + m - 2 : ℕ)) : ℤ) = (j : ℤ) + l + m - 2 by omega] at heb
  have harange := G.hR k ha
  have hbrange := G.hL k' hb
  have hva : 1 ≤ a ∧ a ≤ (G.v : ℤ) := ⟨harange.1, harange.2⟩
  have hvb : 1 ≤ b ∧ b ≤ (G.v : ℤ) := ⟨hbrange.1, hbrange.2⟩
  have hv : (G.v : ℤ) ≤ G.lbZ := G.v_le_lbZ
  have hpos := G.lbZ_pos
  have hsplit : (k : ℤ) * G.lbZ = ((k : ℤ) - 1) * G.lbZ + G.lbZ := by ring
  have hkk : k = k' := by
    by_contra hne
    -- first, `k ≤ k'`
    have hle : k ≤ k' := by
      by_contra hcon
      push_neg at hcon
      have h1 : (k' : ℤ) ≤ (k : ℤ) - 1 := by
        have : (k' : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hcon
        omega
      have h2 : (k' : ℤ) * G.lbZ ≤ ((k : ℤ) - 1) * G.lbZ :=
        mul_le_mul_of_nonneg_right h1 hpos.le
      have : (1 : ℤ) ≤ l := by exact_mod_cast hl
      have : (1 : ℤ) ≤ m := by exact_mod_cast hm
      omega
    have hlt : k < k' := by omega
    -- the pair of arrows at the boundary `k * lb` excludes this
    have hbnd : ((k * G.lb : ℕ) : ℤ) = (k : ℤ) * G.lbZ := by
      unfold GapSpec.lbZ; push_cast; ring
    have hmemL : (k * G.lb) ∈ G.marking.topArrowL := by
      rw [GapSpec.mem_topArrowL]; exact Or.inl ⟨k, hk1, by omega, hbnd⟩
    have hmemR : (k * G.lb) ∈ G.marking.topArrowR := by
      rw [GapSpec.mem_topArrowR]; exact Or.inl ⟨k, hk1, by omega, hbnd⟩
    have hk'k : (k : ℤ) * G.lbZ + G.lbZ ≤ (k' : ℤ) * G.lbZ := by
      have h1 : (k : ℤ) + 1 ≤ (k' : ℤ) := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_right h1 hpos.le
      linarith [this, (by ring : ((k : ℤ) + 1) * G.lbZ = (k : ℤ) * G.lbZ + G.lbZ)]
    have hlow : (j : ℤ) - 1 ≤ ((k * G.lb : ℕ) : ℤ) := by rw [hbnd]; linarith
    have hhigh : ((k * G.lb : ℕ) : ℤ) ≤ (j : ℤ) + l + m - 3 := by
      rw [hbnd]; linarith
    by_cases hcase : ((k * G.lb : ℕ) : ℤ) ≤ (j : ℤ) + l - 2
    · exact absurd (topArrowL_effect hM hg hmemL hlow hcase) (by simp)
    · push_neg at hcase
      exact absurd (topArrowR_effect hM hg hmemR (by omega) hhigh) (by simp)
  subst hkk
  exact ⟨k, a, b, ⟨hk1, hk2, ha, hb, hea, heb⟩⟩

/-- The pair of arrows inside a bucket confines the length of the left part of a gap lying
above it to the range prescribed by the interval of the bucket.  (When the interval is so far
from `0` that no gap at all is possible, the extra arrows of the marking rule the gap out and
the statement holds vacuously.) -/
lemma length_bounds (hM : S.RespectsMarking G.marking) {r u : ℤ} {l m j k : ℕ} {a b : ℤ}
    (hg : S.GapData r u l m j) (hd : Bucketed G l m j k a b) :
    (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + a - G.Imax k ≤ l ∧
      (l : ℤ) ≤ (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + a - G.Imin k := by
  have hl' : (1 : ℤ) ≤ l := by exact_mod_cast hg.toGapAt.l_pos
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hg.toGapAt.m_pos
  have hva := hd.a_mem
  have hvb := hd.b_mem
  have hv : (G.v : ℤ) ≤ G.lbZ := G.v_le_lbZ
  have hpos := G.lbZ_pos
  have h2v := G.two_v_le_lbZ
  have hlb := G.lbZ_eq
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hd.k_pos
  have hks : (k : ℤ) ≤ (G.s : ℤ) := by exact_mod_cast hd.k_le
  have heL := hd.eL
  have heR := hd.eR
  -- the products that occur, and the linear facts relating them
  have hsplit : (k : ℤ) * G.lbZ = ((k : ℤ) - 1) * G.lbZ + G.lbZ := by ring
  have hP0 : 0 ≤ ((k : ℤ) - 1) * G.lbZ := mul_nonneg (by linarith) hpos.le
  have hQ0 : 0 ≤ (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
  have hQle : (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hImin := G.hImin k
  have hImax := G.hImax k
  have hIk := G.hI k
  constructor
  · -- the right-facing arrow of the bucket gives the lower bound on `l`
    set B : ℤ := ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v - 1 - G.Imax k
      with hB
    have hB0 : 0 ≤ B := by rw [hB]; linarith
    have hBmem : B.toNat ∈ G.marking.topArrowR := by
      rw [GapSpec.mem_topArrowR]
      exact Or.inr (Or.inl ⟨k, hd.k_pos, hd.k_le, by rw [Int.toNat_of_nonneg hB0]⟩)
    have hBcast : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hB0
    by_cases hcase : B ≤ (j : ℤ) + l + m - 3
    · by_contra hcon
      push_neg at hcon
      refine topArrowR_effect hM hg hBmem ?_ ?_
      · rw [hBcast, hB]; linarith
      · rw [hBcast]; exact hcase
    · -- the arrow lies to the right of the gap; then `k = s`, and an extra arrow forbids the gap
      push_neg at hcase
      exfalso
      rw [hB] at hcase
      have hks' : k = G.s := by
        by_contra hne
        have hklt : (k : ℤ) ≤ (G.s : ℤ) - 1 := by
          have h0 : k < G.s := by omega
          have : (k : ℤ) + 1 ≤ (G.s : ℤ) := by exact_mod_cast h0
          linarith
        have h1 : (2 * (G.v : ℤ) - 1) * (k : ℤ) ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) :=
          mul_le_mul_of_nonneg_left hklt (by linarith)
        have h2 : (2 * (G.v : ℤ) - 1) * (k : ℤ)
            = (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + (2 * (G.v : ℤ) - 1) := by ring
        linarith
      have hbb : b < - G.Imax G.s := by rw [← hks']; linarith
      have hE : (G.s : ℤ) * G.lbZ - G.v + b - 1 = (j : ℤ) + l + m - 3 := by
        rw [← hks']; linarith
      have hE0 : 0 ≤ (G.s : ℤ) * G.lbZ - G.v + b - 1 := by rw [hE]; linarith
      have hEmem : ((G.s : ℤ) * G.lbZ - G.v + b - 1).toNat ∈ G.marking.topArrowR := by
        rw [GapSpec.mem_topArrowR]
        exact Or.inr (Or.inr ⟨b, hvb.1, hvb.2, hbb, by rw [Int.toNat_of_nonneg hE0]⟩)
      have hEcast : ((((G.s : ℤ) * G.lbZ - G.v + b - 1).toNat : ℕ) : ℤ)
          = (G.s : ℤ) * G.lbZ - G.v + b - 1 := Int.toNat_of_nonneg hE0
      refine topArrowR_effect hM hg hEmem ?_ ?_
      · rw [hEcast, hE]; linarith
      · rw [hEcast, hE]
  · -- the left-facing arrow of the bucket gives the upper bound on `l`
    set A : ℤ := ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v + 1 - G.Imin k
      with hA
    have hA0 : 0 ≤ A := by rw [hA]; linarith
    have hAmem : A.toNat ∈ G.marking.topArrowL := by
      rw [GapSpec.mem_topArrowL]
      exact Or.inr (Or.inl ⟨k, hd.k_pos, hd.k_le, by rw [Int.toNat_of_nonneg hA0]⟩)
    have hAcast : ((A.toNat : ℕ) : ℤ) = A := Int.toNat_of_nonneg hA0
    by_cases hcase : (j : ℤ) - 1 ≤ A
    · by_contra hcon
      push_neg at hcon
      refine topArrowL_effect hM hg hAmem ?_ ?_
      · rw [hAcast]; exact hcase
      · rw [hAcast, hA]; linarith
    · -- the arrow lies to the left of the gap; then `k = 1`, and an extra arrow forbids the gap
      push_neg at hcase
      exfalso
      rw [hA] at hcase
      have hk1' : k = 1 := by
        by_contra hne
        have hkge : (2 : ℤ) ≤ (k : ℤ) := by
          have h0 : 2 ≤ k := by omega
          exact_mod_cast h0
        have h1 : (2 * (G.v : ℤ) - 1) * 1 ≤ (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      have hzeroP : ((k : ℤ) - 1) * G.lbZ = 0 := by rw [hk1']; norm_num
      have hzeroQ : (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) = 0 := by rw [hk1']; norm_num
      have haa : a < G.Imin 1 := by rw [← hk1']; linarith
      have hE : (G.v : ℤ) + 1 - a = (j : ℤ) - 1 := by linarith
      have hE0 : 0 ≤ (G.v : ℤ) + 1 - a := by linarith
      have hEmem : ((G.v : ℤ) + 1 - a).toNat ∈ G.marking.topArrowL := by
        rw [GapSpec.mem_topArrowL]
        exact Or.inr (Or.inr ⟨a, hva.1, hva.2, haa, by rw [Int.toNat_of_nonneg hE0]⟩)
      have hEcast : (((((G.v : ℤ) + 1 - a).toNat) : ℕ) : ℤ) = (G.v : ℤ) + 1 - a :=
        Int.toNat_of_nonneg hE0
      refine topArrowL_effect hM hg hEmem ?_ ?_
      · rw [hEcast, hE]
      · rw [hEcast, hE]; linarith

end Schematic

end StickPolyhex
