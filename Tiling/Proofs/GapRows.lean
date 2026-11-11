import Tiling.Proofs.GapDecode

/-!
# The bucket is constant along a row, and the state cycles

This file proves, for a schematic respecting the marks of Section 2.5, the two lemmas
`lem:gapsinsamebucket` and `lem:leftandrightsidelengths` of the paper:

* `Schematic.block_relation`: for a block `X` of the row `r` with the gaps `G₁` on its left and
  `G₂` on its right and the gap `G'` of the row `r - 1` below it, the gaps `G₁` and `G₂` lie
  above buckets with the same index `i`, and the pair of arrows on the bottom face of `X` fixes
  the lengths of the two parts of `G'`: they are `(2v-1)(σ i - 1) + b₁` and
  `(2v-1)(s - σ i) + a₂`, where `b₁` is the value read at the right end of `G₁` and `a₂` the
  value read at the left end of `G₂`;
* `Schematic.row_bucket_eq`: all the gaps of a row lie above buckets with the same index;
* `Schematic.exists_state`: hence each row has a well-defined state.
-/

namespace StickPolyhex

namespace GapSpec

variable (G : GapSpec)

lemma lbZ_mono {p q : ℕ} (h : p ≤ q) : (p : ℤ) * G.lbZ ≤ (q : ℤ) * G.lbZ :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) G.lbZ_pos.le

lemma lbZ_step {p q : ℕ} (h : p < q) : (p : ℤ) * G.lbZ + G.lbZ ≤ (q : ℤ) * G.lbZ := by
  have h1 : ((p : ℤ) + 1) * G.lbZ ≤ (q : ℤ) * G.lbZ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h) G.lbZ_pos.le
  linarith [h1, (by ring : ((p : ℤ) + 1) * G.lbZ = (p : ℤ) * G.lbZ + G.lbZ)]

end GapSpec

namespace Schematic

variable {G : GapSpec} {S : Schematic G.blockLen}

/-- The relation between the two gaps of a row adjacent to a block and the gap of the row below
that block: the two gaps lie above the same bucket, and the lengths of the two parts of the gap
below are determined by the values read at the two ends of the block. -/
lemma block_relation (hM : S.RespectsMarking G.marking) {r c u₁ : ℤ}
    {l₁ m₁ j₁ k₁ : ℕ} {a₁ b₁ : ℤ} {l₂ m₂ j₂ k₂ : ℕ} {a₂ b₂ : ℤ} {l' m' : ℕ}
    (hc : S.slot r c = .block 0)
    (he₁ : u₁ + l₁ + m₁ = c) (hd₁ : Bucketed G l₁ m₁ j₁ k₁ a₁ b₁)
    (hg₂ : S.GapData r (c + G.blockLen + 1) l₂ m₂ j₂) (hd₂ : Bucketed G l₂ m₂ j₂ k₂ a₂ b₂)
    (hg' : S.GapAt (r - 1) (u₁ - j₁ + G.blockLen + 1) l' m')
    (he' : (u₁ - j₁ + G.blockLen + 1) + l' + m' = c + G.blockLen + 1 - j₂) :
    k₁ = k₂ ∧ (l' : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.sigma k₁ : ℤ) - 1) + b₁ ∧
      (m' : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (G.sigma k₁ : ℤ)) + a₂ := by
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hv := G.v_le_lbZ
  have h2v := G.two_v_le_lbZ
  have hpos := G.lbZ_pos
  have hlb := G.lbZ_eq
  have hn := G.blockLenZ
  have ha₁ := hd₁.a_mem; have hb₁ := hd₁.b_mem
  have ha₂ := hd₂.a_mem; have hb₂ := hd₂.b_mem
  have hj₂ : (2 : ℤ) ≤ j₂ := by exact_mod_cast hg₂.two_le
  have hl' : (1 : ℤ) ≤ l' := by exact_mod_cast hg'.l_pos
  have hm' : (1 : ℤ) ≤ m' := by exact_mod_cast hg'.m_pos
  have he₁' := hd₁.eR
  have he₂' := hd₂.eL
  -- the first claim: the two gaps lie above the same bucket
  have hsame : k₁ = k₂ := by
    obtain ⟨j', hj'⟩ := exists_gapData hg'
    obtain ⟨k', a', b', hd'⟩ := decode hM hj'
    have hlen := hd'.length
    have ha' := hd'.a_mem
    have hb' := hd'.b_mem
    have hsum : (l' : ℤ) + m' = (k₁ : ℤ) * G.lbZ - ((k₂ : ℤ) - 1) * G.lbZ - 2 * G.v + a₂ + b₁ := by
      have : ((u₁ - j₁ + G.blockLen + 1) : ℤ) + l' + m' = c + G.blockLen + 1 - j₂ := he'
      linarith [this, he₁', he₂', he₁]
    rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
    · exfalso
      have := G.lbZ_step hlt
      have hspl : (k₂ : ℤ) * G.lbZ = ((k₂ : ℤ) - 1) * G.lbZ + G.lbZ := by ring
      linarith
    · exact heq
    · exfalso
      have := G.lbZ_step hgt
      have hspl : (k₂ : ℤ) * G.lbZ = ((k₂ : ℤ) - 1) * G.lbZ + G.lbZ := by ring
      linarith
  subst hsame
  -- the position of the gap below the block, measured on the bottom face of the block
  set q : ℤ := (u₁ - j₁ + G.blockLen + 1) - c with hq
  have hqval : q = ((G.s : ℤ) - k₁) * G.lbZ + G.v + 1 - b₁ := by
    have hspl : ((G.s : ℤ) - k₁) * G.lbZ = (G.s : ℤ) * G.lbZ - (k₁ : ℤ) * G.lbZ := by ring
    rw [hq]; linarith [he₁', he₁, hn, hspl]
  -- the pair of arrows on the bottom face of the block, for the state `k₁`
  set Q : ℤ := ((G.s : ℤ) - k₁) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((G.sigma k₁ : ℤ) - 1) + G.v - 1
    with hQ
  have hsig := G.sigma_mem hd₁.k_pos hd₁.k_le
  have hsig1 : (1 : ℤ) ≤ (G.sigma k₁ : ℤ) := by exact_mod_cast hsig.1
  have hsigs : ((G.sigma k₁ : ℕ) : ℤ) ≤ (G.s : ℤ) := by exact_mod_cast hsig.2
  have hSk : 0 ≤ ((G.s : ℤ) - k₁) * G.lbZ := by
    have : (k₁ : ℤ) ≤ (G.s : ℤ) := by exact_mod_cast hd₁.k_le
    exact mul_nonneg (by linarith) hpos.le
  have hW0 : 0 ≤ (2 * (G.v : ℤ) - 1) * ((G.sigma k₁ : ℤ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hWle : (2 * (G.v : ℤ) - 1) * ((G.sigma k₁ : ℤ) - 1) ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hQ0 : 0 ≤ Q := by rw [hQ]; linarith
  have hQnat : ((Q.toNat : ℕ) : ℤ) = Q := Int.toNat_of_nonneg hQ0
  have hQmemR : Q.toNat ∈ G.marking.botArrowR := by
    rw [GapSpec.mem_botArrowR]
    exact ⟨k₁, hd₁.k_pos, hd₁.k_le, by rw [hQnat, hQ]⟩
  have hQmemL : (Q + 2).toNat ∈ G.marking.botArrowL := by
    rw [GapSpec.mem_botArrowL]
    refine ⟨k₁, hd₁.k_pos, hd₁.k_le, ?_⟩
    rw [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ Q + 2), hQ]
    ring
  have hQ2nat : (((Q + 2).toNat : ℕ) : ℤ) = Q + 2 :=
    Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ Q + 2)
  have hend : (u₁ - j₁ + G.blockLen + 1) + l' + m' - 1 ≤ c + G.blockLen := by
    rw [he']; linarith
  -- the total length of the gap below the block
  have hsum' : (l' : ℤ) + m' = G.lbZ - 2 * G.v + a₂ + b₁ := by
    have hspl : (k₁ : ℤ) * G.lbZ = ((k₁ : ℤ) - 1) * G.lbZ + G.lbZ := by ring
    have : ((u₁ - j₁ + G.blockLen + 1) : ℤ) + l' + m' = c + G.blockLen + 1 - j₂ := he'
    linarith [this, he₁', he₂', he₁]
  -- the right-facing arrow gives `Q ≤ q + l' - 2`
  have hQle : Q ≤ q + l' - 2 := by
    by_contra hcon
    push_neg at hcon
    refine botArrowR_effect hM hc hg' hQmemR ?_ ?_ hend
    · rw [hQnat, hq] at *; linarith
    · rw [hQnat]
      have : q + l' + m' - 2 = (u₁ - j₁ + G.blockLen + 1) + l' + m' - 2 - c := by rw [hq]; ring
      rw [hq] at *
      linarith [hsum', hqval, hWle]
  -- the left-facing arrow gives `q + l' - 2 ≤ Q`
  have hQge : q + l' - 2 ≤ Q := by
    by_contra hcon
    push_neg at hcon
    refine botArrowL_effect hM hc hg' hQmemL ?_ ?_ hend
    · rw [hQ2nat, hq] at *; linarith
    · rw [hQ2nat, hq] at *; linarith
  have hl'val : (l' : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.sigma k₁ : ℤ) - 1) + b₁ := by
    have : Q = q + l' - 2 := le_antisymm hQle hQge
    rw [hQ] at this
    rw [hqval] at this
    linarith
  refine ⟨rfl, hl'val, ?_⟩
  have hring : (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1)
      = (2 * (G.v : ℤ) - 1) * ((G.sigma k₁ : ℤ) - 1)
        + (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (G.sigma k₁ : ℤ)) := by ring
  linarith [hsum', hl'val, hlb, hring]

/-- Two gaps of the same row lie above buckets with the same index — the paper's
`lem:gapsinsamebucket`. -/
lemma row_bucket_eq_aux (hM : S.RespectsMarking G.marking) (d : ℕ) :
    ∀ (r u ũ : ℤ) (l m j k l2 m2 j2' k2 : ℕ) (a b a2 b2 : ℤ), ũ = u + d →
      S.GapData r u l m j → Bucketed G l m j k a b →
      S.GapData r ũ l2 m2 j2' → Bucketed G l2 m2 j2' k2 a2 b2 → k = k2 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro r u ũ l m j k l2 m2 j2' k2 a b a2 b2 hd hg hb hg2 hb2
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      simp only [Nat.cast_zero, add_zero] at hd
      subst hd
      obtain ⟨hl, hm⟩ := GapAt.unique hg.toGapAt hg2.toGapAt
      subst hl; subst hm
      have hj : j = j2' := by
        have h1 := hg.slot_below
        have h2 := hg2.slot_below
        rw [h1] at h2; injection h2
      subst hj
      exact (bucketed_unique hb hb2).1
    · -- the next gap of the row, on the other side of the block that follows `u`
      set c : ℤ := u + l + m with hc0
      have hcblock : S.slot r c = .block 0 := hg.toGapAt.blockRight
      obtain ⟨l₂, m₂, hg₂⟩ := exists_right_gap hcblock
      obtain ⟨j₂, hg₂'⟩ := exists_gapData hg₂
      obtain ⟨k₂, a₂, b₂, hd₂⟩ := decode hM hg₂'
      obtain ⟨l', m', hg', he'⟩ := below_gap hcblock hg rfl hg₂'
      have hstep := block_relation hM hcblock rfl hb hg₂' hd₂ hg' he'
      have hnext : c + G.blockLen + 1 ≤ ũ := by
        have := gap_gap_gap hg.toGapAt hg2.toGapAt (by
          have : (0 : ℤ) < d := by exact_mod_cast hdpos
          omega)
        rw [hc0]; push_cast at this ⊢; omega
      have hd' : (ũ - (c + G.blockLen + 1)).toNat < d := by
        have hl1 : (1 : ℤ) ≤ l := by exact_mod_cast hg.toGapAt.l_pos
        have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hg.toGapAt.m_pos
        have hnn : (0 : ℤ) ≤ (G.blockLen : ℤ) := Int.natCast_nonneg _
        have hdz : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
        omega
      have := ih _ hd' r (c + G.blockLen + 1) ũ l₂ m₂ j₂ k₂ l2 m2 j2' k2 a₂ b₂ a2 b2
        (by omega) hg₂' hd₂ hg2 hb2
      rw [hstep.1, this]

/-- Two gaps of the same row lie above buckets with the same index. -/
lemma row_bucket_eq (hM : S.RespectsMarking G.marking) {r u ũ : ℤ} {l m j k l2 m2 j2' k2 : ℕ}
    {a b a2 b2 : ℤ} (hg : S.GapData r u l m j) (hb : Bucketed G l m j k a b)
    (hg2 : S.GapData r ũ l2 m2 j2') (hb2 : Bucketed G l2 m2 j2' k2 a2 b2) : k = k2 := by
  rcases le_total u ũ with hle | hle
  · exact row_bucket_eq_aux hM (ũ - u).toNat r u ũ l m j k l2 m2 j2' k2 a b a2 b2 (by omega)
      hg hb hg2 hb2
  · exact (row_bucket_eq_aux hM (u - ũ).toNat r ũ u l2 m2 j2' k2 l m j k a2 b2 a b (by omega)
      hg2 hb2 hg hb).symm

/-- Every row of a schematic contains a gap, with all its data. -/
lemma exists_gap_of_row (r : ℤ) : ∃ (u : ℤ) (l m j : ℕ), S.GapData r u l m j := by
  obtain ⟨x, hx⟩ := S.exists_gapL r
  obtain ⟨u, l, m, hgap, -, -⟩ := exists_gapAt_of_isGap (r := r) (x := x) (by rw [hx]; trivial)
  obtain ⟨j, hj⟩ := exists_gapData hgap
  exact ⟨u, l, m, j, hj⟩

/-- Each row has a well-defined state: all the gaps of the row lie above the bucket with that
index. -/
lemma exists_state (hM : S.RespectsMarking G.marking) (r : ℤ) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ G.s ∧
      ∀ (u : ℤ) (l m j k : ℕ) (a b : ℤ), S.GapData r u l m j → Bucketed G l m j k a b → k = i := by
  obtain ⟨u, l, m, j, hg⟩ := exists_gap_of_row (S := S) r
  obtain ⟨k, a, b, hd⟩ := decode hM hg
  exact ⟨k, hd.k_pos, hd.k_le, fun u' l' m' j' k' a' b' hg' hd' =>
    row_bucket_eq hM hg' hd' hg hd⟩

end Schematic

end StickPolyhex
