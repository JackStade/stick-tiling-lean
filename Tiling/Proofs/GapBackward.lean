import Tiling.Proofs.GapForward

/-!
# From the gap conditions to the marks

This file proves the converse direction of the main theorem: a schematic satisfying the gap
conditions of Section 2.5 respects the marks `GapSpec.marking`.

The first step (`Schematic.GapConditions.gap_facts`) collects, for a single gap, all the
numerical information the gap conditions give: the position of its two ends on the block below
(in terms of the values of the two gaps below it), the range of its two values and the interval
condition.  Each clause of `Schematic.RespectsMarking` is then a computation with these numbers.
-/

namespace StickPolyhex

namespace GapSpec

variable (G : GapSpec)

/-- A position of the bucket `kb ≠ k` lies outside the open bucket `k`. -/
lemma bucket_out {kb k : ℤ} (hkb1 : 1 ≤ kb) (hkbs : kb ≤ G.s) (hne : kb ≠ k) {t : ℤ}
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * G.v) :
    (kb - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * (kb - 1) + t ≤ (k - 1) * G.lbZ ∨
      k * G.lbZ ≤ (kb - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * (kb - 1) + t := by
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hpos := G.lbZ_pos
  have hlb := G.lbZ_eq
  rcases lt_or_gt_of_ne hne with h | h
  · left
    have h1 : (kb - 1) * G.lbZ + G.lbZ ≤ (k - 1) * G.lbZ := by
      have := mul_le_mul_of_nonneg_right (show (kb - 1) + 1 ≤ k - 1 by omega) hpos.le
      linarith [this, (by ring : ((kb - 1) + 1) * G.lbZ = (kb - 1) * G.lbZ + G.lbZ)]
    have h2 : (2 * (G.v : ℤ) - 1) * (kb - 1) ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith
  · right
    have h1 : k * G.lbZ ≤ (kb - 1) * G.lbZ :=
      mul_le_mul_of_nonneg_right (by omega) hpos.le
    have h2 : 0 ≤ (2 * (G.v : ℤ) - 1) * (kb - 1) := mul_nonneg (by omega) (by omega)
    linarith

/-- A boundary between two buckets lies outside the open bucket `k`. -/
lemma boundary_out {kb k : ℤ} :
    kb * G.lbZ ≤ (k - 1) * G.lbZ ∨ k * G.lbZ ≤ kb * G.lbZ := by
  rcases le_or_gt kb (k - 1) with h | h
  · exact Or.inl (mul_le_mul_of_nonneg_right h G.lbZ_pos.le)
  · exact Or.inr (mul_le_mul_of_nonneg_right (by omega) G.lbZ_pos.le)

/-- A position of the bottom face associated with the state `e ≠ f` lies outside the range
covered by the gap below the bucket associated with the state `f`. -/
lemma bottom_out {e f w t : ℤ} (hef : e ≠ f) (hw0 : 0 ≤ w) (hw : w ≤ G.lbZ - 2 * G.v)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2 * G.v) :
    e * G.lbZ + w + t ≤ f * G.lbZ ∨ (f + 1) * G.lbZ ≤ e * G.lbZ + w + t := by
  have hpos := G.lbZ_pos
  rcases lt_or_gt_of_ne hef with h | h
  · left
    have h1 : (e + 1) * G.lbZ ≤ f * G.lbZ := mul_le_mul_of_nonneg_right (by omega) hpos.le
    linarith [h1, (by ring : (e + 1) * G.lbZ = e * G.lbZ + G.lbZ)]
  · right
    have h1 : (f + 1) * G.lbZ ≤ e * G.lbZ := mul_le_mul_of_nonneg_right (by omega) hpos.le
    linarith

/-- A strict form of `bottom_out`, for the positions of the right-facing arrows of the bottom
face. -/
lemma bottom_out_strict {e f w t : ℤ} (hef : e ≠ f) (hw0 : 0 ≤ w) (hw : w ≤ G.lbZ - 2 * G.v)
    (ht0 : 1 ≤ t) (ht2 : t ≤ 2 * G.v - 1) :
    e * G.lbZ + w + t < f * G.lbZ ∨ (f + 1) * G.lbZ < e * G.lbZ + w + t := by
  have hpos := G.lbZ_pos
  rcases lt_or_gt_of_ne hef with h | h
  · left
    have h1 : (e + 1) * G.lbZ ≤ f * G.lbZ := mul_le_mul_of_nonneg_right (by omega) hpos.le
    linarith [h1, (by ring : (e + 1) * G.lbZ = e * G.lbZ + G.lbZ)]
  · right
    have h1 : (f + 1) * G.lbZ ≤ e * G.lbZ := mul_le_mul_of_nonneg_right (by omega) hpos.le
    linarith

end GapSpec

namespace Schematic

variable {G : GapSpec} {S : Schematic G.blockLen} {st : ℤ → ℕ}

/-! ### Locating a gap column inside its gap -/

lemma gap_of_gapL {ρ x : ℤ} (h : S.slot ρ x = .gapL) :
    ∃ (u : ℤ) (l m j c : ℕ), S.GapData ρ u l m j ∧ c < l ∧ x = u + c := by
  obtain ⟨u, l, m, hgap, h1, h2⟩ := exists_gapAt_of_isGap (r := ρ) (x := x) (by rw [h]; trivial)
  obtain ⟨j, hg⟩ := exists_gapData hgap
  refine ⟨u, l, m, j, (x - u).toNat, hg, ?_, by omega⟩
  by_contra hcon
  push_neg at hcon
  have := hgap.slot_gapR (k := (x - u).toNat - l) (by omega)
  rw [show u + (l : ℤ) + (((x - u).toNat - l : ℕ) : ℤ) = x by omega, h] at this
  exact Slot.noConfusion this

lemma gap_of_gapR {ρ x : ℤ} (h : S.slot ρ x = .gapR) :
    ∃ (u : ℤ) (l m j c : ℕ), S.GapData ρ u l m j ∧ c < m ∧ x = u + l + c := by
  obtain ⟨u, l, m, hgap, h1, h2⟩ := exists_gapAt_of_isGap (r := ρ) (x := x) (by rw [h]; trivial)
  obtain ⟨j, hg⟩ := exists_gapData hgap
  have hxl : u + (l : ℤ) ≤ x := by
    by_contra hcon
    push_neg at hcon
    have := hgap.slot_gapL (k := (x - u).toNat) (by omega)
    rw [show u + (((x - u).toNat : ℕ) : ℤ) = x by omega, h] at this
    exact Slot.noConfusion this
  exact ⟨u, l, m, j, (x - u - l).toNat, hg, by omega, by omega⟩

/-- The gap of a row below a block, seen from the gap of that row on the left of the block. -/
lemma left_gap_of_below {ρ c u' : ℤ} {l' m' j' : ℕ} (hc : S.slot ρ c = .block 0)
    (hg' : S.GapData (ρ - 1) u' l' m' j') (hin1 : c ≤ u')
    (hin2 : u' + l' + m' - 1 ≤ c + G.blockLen) :
    ∃ (u₁ : ℤ) (l₁ m₁ j₁ : ℕ), S.GapData ρ u₁ l₁ m₁ j₁ ∧ u₁ + l₁ + m₁ = c ∧
      u' = u₁ - j₁ + G.blockLen + 1 := by
  obtain ⟨u₁, l₁, m₁, hgap₁, he₁⟩ := exists_left_gap hc
  obtain ⟨j₁, hg₁⟩ := exists_gapData hgap₁
  obtain ⟨l'', m'', hgap'', hs, he⟩ := below_gap_start hc hg₁ he₁
  exact ⟨u₁, l₁, m₁, j₁, hg₁, he₁,
    (gap_below_unique hgap'' hg'.toGapAt hs he hin1 hin2).symm⟩

/-! ### What the gap conditions say about a single gap -/

/-- All the numerical information carried by the gap conditions about a single gap. -/
lemma GapConditions.gap_facts (hGC : S.GapConditions G st) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) :
    ∃ a b : ℤ, a ∈ G.R (st (r - 1)) ∧ b ∈ G.L (st (r - 1)) ∧
      (j : ℤ) - 2 = ((st (r - 1) : ℤ) - 1) * G.lbZ + G.v - a ∧
      (j : ℤ) + l + m - 2 = (st (r - 1) : ℤ) * G.lbZ - G.v + b ∧
      G.lval (st (r - 1)) l ∈ G.L (st r) ∧ G.rval (st (r - 1)) m ∈ G.R (st r) ∧
      G.Imin (st (r - 1)) ≤ a - G.lval (st (r - 1)) l ∧
      a - G.lval (st (r - 1)) l ≤ G.Imax (st (r - 1)) := by
  have hbelow : S.slot (r - 1) (u - j) = .block 0 := S.slot_block_zero hg.slot_below
  obtain ⟨uY, lY, mY, hgapY, heY⟩ := exists_left_gap hbelow
  obtain ⟨jY, hgY⟩ := exists_gapData hgapY
  obtain ⟨lZ, mZ, hgapZ⟩ := exists_right_gap hbelow
  obtain ⟨jZ, hgZ⟩ := exists_gapData hgapZ
  have hgZ' : S.GapData (r - 1) (u - j + G.blockLen + 1) lZ mZ jZ := by
    rw [show u - (j : ℤ) + G.blockLen + 1 = u - (j : ℤ) + G.blockLen + 1 by ring]
    exact hgZ
  have hr2 : r - 1 - 1 = r - 2 := by ring
  refine ⟨G.rval (st (r - 2)) mY, G.lval (st (r - 2)) lZ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hGC.right_value (r - 1) uY lY mY jY hgY
    rwa [hr2] at this
  · have := hGC.left_value (r - 1) (u - j + G.blockLen + 1) lZ mZ jZ hgZ'
    rwa [hr2] at this
  · exact hGC.align_left r u l m j hg uY lY mY jY hgY heY
  · exact hGC.align_right r u l m j hg lZ mZ jZ hgZ'
  · exact hGC.left_value r u l m j hg
  · exact hGC.right_value r u l m j hg
  · exact (hGC.interval r u l m j hg uY lY mY jY hgY heY).1
  · exact (hGC.interval r u l m j hg uY lY mY jY hgY heY).2


/-! ### Position bounds for a gap -/

/-- The four inequalities the gap conditions impose on the position of a gap relative to the
bucket it lies above: its two ends lie strictly inside the bucket, and its change of direction
lies in the range prescribed by the interval of the bucket. -/
lemma GapConditions.gap_bounds (hGC : S.GapConditions G st) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) :
    ((st (r - 1) : ℤ) - 1) * G.lbZ + 1 ≤ (j : ℤ) - 1 ∧
      (j : ℤ) + l + m - 3 ≤ (st (r - 1) : ℤ) * G.lbZ - 1 ∧
      (j : ℤ) + l - 2 ≤ ((st (r - 1) : ℤ) - 1) * G.lbZ
        + (2 * (G.v : ℤ) - 1) * ((st (r - 1) : ℤ) - 1) + G.v - G.Imin (st (r - 1)) ∧
      ((st (r - 1) : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((st (r - 1) : ℤ) - 1) + G.v
        - G.Imax (st (r - 1)) ≤ (j : ℤ) + l - 2 := by
  obtain ⟨a, b, ha, hb, eL, eR, -, -, hi1, hi2⟩ := hGC.gap_facts hg
  have hav := G.hR _ ha
  have hbv := G.hL _ hb
  unfold GapSpec.lval at hi1 hi2
  exact ⟨by linarith [hav.1, hav.2], by linarith [hbv.1, hbv.2], by linarith, by linarith⟩

/-! ### The arrows of the top face -/

/-- No arrow mark of the top face lies in the range spanned by the left part of a gap. -/
lemma topArrowL_excluded (hGC : S.GapConditions G st) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) {p : ℤ} (h1 : (j : ℤ) - 1 ≤ p) (h2 : p ≤ (j : ℤ) + l - 2)
    (hmem : (∃ k : ℕ, 1 ≤ k ∧ k < G.s ∧ p = (k : ℤ) * G.lbZ) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧
        p = ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v + 1 - G.Imin k) ∨
      (∃ a : ℤ, 1 ≤ a ∧ a ≤ (G.v : ℤ) ∧ a < G.Imin 1 ∧ p = (G.v : ℤ) + 1 - a)) : False := by
  obtain ⟨hlow, hhigh, hup, -⟩ := hGC.gap_bounds hg
  set k := st (r - 1) with hkdef
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hg.toGapAt.m_pos
  have hpos := G.lbZ_pos
  have h2v := G.two_v_le_lbZ
  have hsplit : (k : ℤ) * G.lbZ = ((k : ℤ) - 1) * G.lbZ + G.lbZ := by ring
  have hp_low : ((k : ℤ) - 1) * G.lbZ + 1 ≤ p := by linarith
  have hp_high : p ≤ (k : ℤ) * G.lbZ - 1 := by linarith
  have hp_up : p ≤ ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v
      - G.Imin k := by linarith
  rcases hmem with ⟨kb, hkb1, hkbs, hpe⟩ | ⟨kb, hkb1, hkbs, hpe⟩ | ⟨a0, ha1, ha2, ha3, hpe⟩
  · rcases G.boundary_out (kb := (kb : ℤ)) (k := (k : ℤ)) with h | h <;> linarith
  · by_cases hkbk : kb = k
    · rw [hkbk] at hpe
      linarith
    · have hI1 := G.hImin kb
      have hI2 := G.hImax kb
      have hI3 := G.hI kb
      have hne : (kb : ℤ) ≠ (k : ℤ) := by exact_mod_cast hkbk
      rcases G.bucket_out (kb := (kb : ℤ)) (k := (k : ℤ)) (by exact_mod_cast hkb1)
        (by exact_mod_cast hkbs) hne (t := (G.v : ℤ) + 1 - G.Imin kb) (by linarith)
        (by linarith) with h | h <;> linarith
  · by_cases hk1 : k = 1
    · have h0 : (k : ℤ) - 1 = 0 := by rw [hk1]; norm_num
      have e1 : ((k : ℤ) - 1) * G.lbZ = 0 := by rw [h0]; ring
      have e2 : (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) = 0 := by rw [h0]; ring
      have e3 : G.Imin k = G.Imin 1 := by rw [hk1]
      linarith
    · have hk2 : (2 : ℤ) ≤ (k : ℤ) := by
        have : 2 ≤ k := by
          have := (hGC.state_mem (r - 1)).1
          omega
        exact_mod_cast this
      have hmul : G.lbZ ≤ ((k : ℤ) - 1) * G.lbZ := by
        have := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ (k : ℤ) - 1 by linarith) hpos.le
        linarith [this, (by ring : (1 : ℤ) * G.lbZ = G.lbZ)]
      linarith

/-- No arrow mark of the top face lies in the range spanned by the right part of a gap. -/
lemma topArrowR_excluded (hGC : S.GapConditions G st) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) {p : ℤ} (h1 : (j : ℤ) + l - 2 ≤ p) (h2 : p ≤ (j : ℤ) + l + m - 3)
    (hmem : (∃ k : ℕ, 1 ≤ k ∧ k < G.s ∧ p = (k : ℤ) * G.lbZ) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ G.s ∧
        p = ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v - 1 - G.Imax k) ∨
      (∃ b : ℤ, 1 ≤ b ∧ b ≤ (G.v : ℤ) ∧ b < - G.Imax G.s ∧
        p = (G.s : ℤ) * G.lbZ - G.v + b - 1)) : False := by
  obtain ⟨hlow, hhigh, -, hlow2⟩ := hGC.gap_bounds hg
  set k := st (r - 1) with hkdef
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hl1 : (1 : ℤ) ≤ l := by exact_mod_cast hg.toGapAt.l_pos
  have hpos := G.lbZ_pos
  have h2v := G.two_v_le_lbZ
  have hlbeq := G.lbZ_eq
  have hsplit : (k : ℤ) * G.lbZ = ((k : ℤ) - 1) * G.lbZ + G.lbZ := by ring
  have hp_low : ((k : ℤ) - 1) * G.lbZ + 1 ≤ p := by linarith
  have hp_high : p ≤ (k : ℤ) * G.lbZ - 1 := by linarith
  have hp_low2 : ((k : ℤ) - 1) * G.lbZ + (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) + G.v
      - G.Imax k ≤ p := by linarith
  have hkm := hGC.state_mem (r - 1)
  rcases hmem with ⟨kb, hkb1, hkbs, hpe⟩ | ⟨kb, hkb1, hkbs, hpe⟩ | ⟨b0, hb1, hb2, hb3, hpe⟩
  · rcases G.boundary_out (kb := (kb : ℤ)) (k := (k : ℤ)) with h | h <;> linarith
  · by_cases hkbk : kb = k
    · rw [hkbk] at hpe
      linarith
    · have hI1 := G.hImin kb
      have hI2 := G.hImax kb
      have hI3 := G.hI kb
      have hne : (kb : ℤ) ≠ (k : ℤ) := by exact_mod_cast hkbk
      rcases G.bucket_out (kb := (kb : ℤ)) (k := (k : ℤ)) (by exact_mod_cast hkb1)
        (by exact_mod_cast hkbs) hne (t := (G.v : ℤ) - 1 - G.Imax kb) (by linarith)
        (by linarith) with h | h <;> linarith
  · by_cases hks : k = G.s
    · have hkz : (k : ℤ) = (G.s : ℤ) := by rw [hks]
      have e1 : (2 * (G.v : ℤ) - 1) * ((k : ℤ) - 1) = G.lbZ - 2 * G.v := by
        rw [hkz, hlbeq]; ring
      have e2 : G.Imax k = G.Imax G.s := by rw [hks]
      have hsplit2 : (G.s : ℤ) * G.lbZ = ((k : ℤ) - 1) * G.lbZ + G.lbZ := by rw [hkz]; ring
      linarith
    · have hklt : (k : ℤ) ≤ (G.s : ℤ) - 1 := by
        have : k < G.s := by omega
        have : (k : ℤ) + 1 ≤ (G.s : ℤ) := by exact_mod_cast this
        linarith
      have hmul : (k : ℤ) * G.lbZ ≤ ((G.s : ℤ) - 1) * G.lbZ :=
        mul_le_mul_of_nonneg_right hklt hpos.le
      have hsplits : (G.s : ℤ) * G.lbZ = ((G.s : ℤ) - 1) * G.lbZ + G.lbZ := by ring
      linarith

/-! ### The gap below a block -/

/-- The position and the two parts of the gap of the row below a block, in terms of the state of
the row of the block and of the two values of that gap. -/
lemma GapConditions.below_gap_position (hGC : S.GapConditions G st) {r c : ℤ}
    (hc : S.slot r c = .block 0) {u' : ℤ} {l' m' j' : ℕ}
    (hg' : S.GapData (r - 1) u' l' m' j') (hin1 : c ≤ u')
    (hin2 : u' + l' + m' - 1 ≤ c + G.blockLen) :
    ∃ x' y' : ℤ, 1 ≤ x' ∧ x' ≤ (G.v : ℤ) ∧ 1 ≤ y' ∧ y' ≤ (G.v : ℤ) ∧
      u' - c = ((G.s : ℤ) - (st (r - 1) : ℤ)) * G.lbZ + G.v + 1 - x' ∧
      (l' : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.sigma (st (r - 1)) : ℤ) - 1) + x' ∧
      (m' : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (G.sigma (st (r - 1)) : ℤ)) + y' := by
  obtain ⟨u₁, l₁, m₁, j₁, hg₁, he₁, hu'⟩ := left_gap_of_below hc hg' hin1 hin2
  have halign := hGC.align_right r u₁ l₁ m₁ j₁ hg₁ l' m' j' (by rw [← hu']; exact hg')
  have hx' := hGC.left_value (r - 1) u' l' m' j' hg'
  have hy' := hGC.right_value (r - 1) u' l' m' j' hg'
  have hcyc : st (r - 1 - 1) = G.sigma (st (r - 1)) := hGC.state_cycle (r - 1)
  rw [show r - 1 - 1 = r - 2 by ring] at hx' hy' hcyc
  refine ⟨G.lval (st (r - 2)) l', G.rval (st (r - 2)) m', (G.hL _ hx').1, (G.hL _ hx').2,
    (G.hR _ hy').1, (G.hR _ hy').2, ?_, ?_, ?_⟩
  · have hbl := G.blockLenZ
    have hprod : ((G.s : ℤ) - (st (r - 1) : ℤ)) * G.lbZ
        = (G.s : ℤ) * G.lbZ - (st (r - 1) : ℤ) * G.lbZ := by ring
    rw [hu', ← he₁]
    linarith
  · rw [GapSpec.lval, hcyc]; ring
  · rw [GapSpec.rval, hcyc]; ring

/-! ### The six clauses -/

lemma respectsMarking_triangleR (hGC : S.GapConditions G st) (i : ℕ) (r x : ℤ)
    (hx : S.slot r x = .block (i + 1)) (habove : S.slot (r + 1) x = .block G.blockLen) :
    i ∈ G.marking.triangleR := by
  obtain ⟨l, m, hgap⟩ := exists_gapAt (S := S) (r := r + 1) (u := x + 1)
    (by rw [show x + 1 - 1 = x by ring]; exact habove)
  obtain ⟨j, hg⟩ := exists_gapData hgap
  have hj2 := hg.two_le
  have hb := hg.slot_below
  rw [show r + 1 - 1 = r by ring] at hb
  have hpred : S.slot r x = .block (j - 1) := by
    refine S.pred_of_block_succ ?_
    rw [show j - 1 + 1 = j by omega]; exact hb
  rw [hx] at hpred
  injection hpred with e
  obtain ⟨a, b, ha, -, eL, -, -, -, -, -⟩ := hGC.gap_facts hg
  rw [show r + 1 - 1 = r by ring] at ha eL
  have hst := hGC.state_mem r
  refine ⟨st r, hst.1, hst.2, a, ha, ?_⟩
  rw [show ((i : ℤ)) = (j : ℤ) - 2 by omega]
  exact eL

lemma respectsMarking_triangleL (hGC : S.GapConditions G st) (i : ℕ) (r x : ℤ)
    (hx : S.slot r x = .block (i + 1)) (habove : S.slot (r + 1) (x + 1) = .block 0) :
    i ∈ G.marking.triangleL := by
  obtain ⟨u, l, m, hgap, he⟩ := exists_left_gap (S := S) (r := r + 1) habove
  obtain ⟨j, hg⟩ := exists_gapData hgap
  have hl := hgap.l_pos
  have hm := hgap.m_pos
  have hbelow := hg.below (c := l + m - 1) (by omega)
  rw [show r + 1 - 1 = r by ring] at hbelow
  rw [show u + (((l + m - 1 : ℕ)) : ℤ) = x by omega, hx] at hbelow
  injection hbelow with e
  obtain ⟨a, b, -, hb, -, eR, -, -, -, -⟩ := hGC.gap_facts hg
  rw [show r + 1 - 1 = r by ring] at hb eR
  have hst := hGC.state_mem r
  refine ⟨st r, hst.1, hst.2, b, hb, ?_⟩
  rw [show ((i : ℤ)) = (j : ℤ) + l + m - 2 by omega]
  exact eR

lemma respectsMarking_topArrowL (hGC : S.GapConditions G st) {i : ℕ}
    (hi : i ∈ G.marking.topArrowL) (r x : ℤ) (hx : S.slot r x = .block (i + 1))
    (hgapL : S.slot (r + 1) x = .gapL) : False := by
  obtain ⟨u, l, m, j, c, hg, hc, hxu⟩ := gap_of_gapL hgapL
  have hm := hg.toGapAt.m_pos
  have hbelow := hg.below (c := c) (by omega)
  rw [show r + 1 - 1 = r by ring, show u + (c : ℤ) = x from hxu.symm, hx] at hbelow
  injection hbelow with e
  refine topArrowL_excluded hGC hg (p := (i : ℤ)) ?_ ?_ ?_
  · have : (i : ℤ) + 1 = (j : ℤ) + c := by exact_mod_cast e
    have : (0 : ℤ) ≤ (c : ℤ) := by positivity
    omega
  · have h1 : (i : ℤ) + 1 = (j : ℤ) + c := by exact_mod_cast e
    have h2 : (c : ℤ) + 1 ≤ (l : ℤ) := by exact_mod_cast hc
    omega
  · exact (GapSpec.mem_topArrowL G).1 hi

lemma respectsMarking_topArrowR (hGC : S.GapConditions G st) {i : ℕ}
    (hi : i ∈ G.marking.topArrowR) (r x : ℤ) (hx : S.slot r x = .block (i + 2))
    (hgapR : S.slot (r + 1) x = .gapR) : False := by
  obtain ⟨u, l, m, j, c, hg, hc, hxu⟩ := gap_of_gapR hgapR
  have hl := hg.toGapAt.l_pos
  have hbelow := hg.below (c := l + c) (by omega)
  rw [show r + 1 - 1 = r by ring,
    show u + (((l + c : ℕ)) : ℤ) = x by rw [hxu]; push_cast; ring, hx] at hbelow
  injection hbelow with e
  refine topArrowR_excluded hGC hg (p := (i : ℤ)) ?_ ?_ ?_
  · have h1 : (i : ℤ) + 2 = (j : ℤ) + (l + c : ℕ) := by exact_mod_cast e
    have h2 : (((l + c : ℕ)) : ℤ) = (l : ℤ) + c := by push_cast; ring
    have : (0 : ℤ) ≤ (c : ℤ) := by positivity
    omega
  · have h1 : (i : ℤ) + 2 = (j : ℤ) + (l + c : ℕ) := by exact_mod_cast e
    have h2 : (((l + c : ℕ)) : ℤ) = (l : ℤ) + c := by push_cast; ring
    have h3 : (c : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hc
    omega
  · exact (GapSpec.mem_topArrowR G).1 hi

lemma respectsMarking_botArrowL (hGC : S.GapConditions G st) {p : ℕ}
    (hp : p ∈ G.marking.botArrowL) (r x : ℤ) (hx : S.slot r x = .block p)
    (hgapL : S.slot (r - 1) x = .gapL) : False := by
  obtain ⟨u', l', m', j', cc, hg', hcc, hxu⟩ := gap_of_gapL hgapL
  have hc : S.slot r (x - (p : ℤ)) = .block 0 := S.slot_block_zero hx
  have hpn : (p : ℤ) ≤ (G.blockLen : ℤ) := by exact_mod_cast S.block_le hx
  have hl' : (1 : ℤ) ≤ l' := by exact_mod_cast hg'.toGapAt.l_pos
  have hm' : (1 : ℤ) ≤ m' := by exact_mod_cast hg'.toGapAt.m_pos
  have hcc' : (cc : ℤ) + 1 ≤ (l' : ℤ) := by exact_mod_cast hcc
  have hcc0 : (0 : ℤ) ≤ (cc : ℤ) := by positivity
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  have hsub := gap_below_subset hc hg'.toGapAt (by omega) (by omega)
  obtain ⟨x', y', hx1, hx2, hy1, hy2, hq, hlq, hmq⟩ :=
    hGC.below_gap_position hc hg' hsub.1 hsub.2
  set e := st (r - 1) with hedef
  have hem := hGC.state_mem (r - 1)
  have hsig := G.sigma_mem hem.1 hem.2
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hpos := G.lbZ_pos
  have hlbeq := G.lbZ_eq
  -- the position `p` lies in the left part of the gap below the block
  have hpq : (p : ℤ) = (u' - (x - (p : ℤ))) + cc := by omega
  have hwe : (2 * (G.v : ℤ) - 1) * ((G.sigma e : ℤ) - 1) ≤ G.lbZ - 2 * G.v := by
    have h1 : (2 * (G.v : ℤ) - 1) * ((G.sigma e : ℤ) - 1)
        ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      have : (G.sigma e : ℤ) ≤ (G.s : ℤ) := by exact_mod_cast hsig.2
      linarith
    linarith
  obtain ⟨i, hi1, hi2, hpe⟩ := hp
  have hsigi := G.sigma_mem hi1 hi2
  by_cases hie : i = e
  · rw [hie] at hpe
    linarith
  · have hne : (G.s : ℤ) - (i : ℤ) ≠ (G.s : ℤ) - (e : ℤ) := by
      have : (i : ℤ) ≠ (e : ℤ) := by exact_mod_cast hie
      omega
    have hwi : (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) ≤ G.lbZ - 2 * G.v := by
      have h1 : (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1)
          ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        have : (G.sigma i : ℤ) ≤ (G.s : ℤ) := by exact_mod_cast hsigi.2
        linarith
      linarith
    have hwi0 : 0 ≤ (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) := by
      refine mul_nonneg (by linarith) ?_
      have : (1 : ℤ) ≤ (G.sigma i : ℤ) := by exact_mod_cast hsigi.1
      linarith
    have hstep : ((G.s : ℤ) - (e : ℤ) + 1) * G.lbZ = ((G.s : ℤ) - (e : ℤ)) * G.lbZ + G.lbZ := by
      ring
    rcases G.bottom_out (e := (G.s : ℤ) - (i : ℤ)) (f := (G.s : ℤ) - (e : ℤ))
      (w := (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1)) (t := (G.v : ℤ) + 1) hne hwi0 hwi
      (by linarith) (by linarith) with h | h <;> linarith

lemma respectsMarking_botArrowR (hGC : S.GapConditions G st) {p : ℕ}
    (hp : p ∈ G.marking.botArrowR) (r x : ℤ) (hx : S.slot r x = .block (p + 1))
    (hgapR : S.slot (r - 1) x = .gapR) : False := by
  obtain ⟨u', l', m', j', cc, hg', hcc, hxu⟩ := gap_of_gapR hgapR
  have hc : S.slot r (x - ((p + 1 : ℕ) : ℤ)) = .block 0 := S.slot_block_zero hx
  have hpn : ((p + 1 : ℕ) : ℤ) ≤ (G.blockLen : ℤ) := by exact_mod_cast S.block_le hx
  have hl' : (1 : ℤ) ≤ l' := by exact_mod_cast hg'.toGapAt.l_pos
  have hm' : (1 : ℤ) ≤ m' := by exact_mod_cast hg'.toGapAt.m_pos
  have hcc' : (cc : ℤ) + 1 ≤ (m' : ℤ) := by exact_mod_cast hcc
  have hcc0 : (0 : ℤ) ≤ (cc : ℤ) := by positivity
  have hpcast : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  have hsub := gap_below_subset hc hg'.toGapAt (by omega) (by omega)
  obtain ⟨x', y', hx1, hx2, hy1, hy2, hq, hlq, hmq⟩ :=
    hGC.below_gap_position hc hg' hsub.1 hsub.2
  set e := st (r - 1) with hedef
  have hem := hGC.state_mem (r - 1)
  have hsig := G.sigma_mem hem.1 hem.2
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hpos := G.lbZ_pos
  have hlbeq := G.lbZ_eq
  have hpq : (p : ℤ) + 1 = (u' - (x - ((p + 1 : ℕ) : ℤ))) + l' + cc := by omega
  have hprod : (2 * (G.v : ℤ) - 1) * ((G.sigma e : ℤ) - 1)
      + (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (G.sigma e : ℤ))
      = (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) := by ring
  have hstep : ((G.s : ℤ) - (e : ℤ) + 1) * G.lbZ = ((G.s : ℤ) - (e : ℤ)) * G.lbZ + G.lbZ := by
    ring
  obtain ⟨i, hi1, hi2, hpe⟩ := hp
  have hsigi := G.sigma_mem hi1 hi2
  by_cases hie : i = e
  · rw [hie] at hpe
    linarith
  · have hne : (G.s : ℤ) - (i : ℤ) ≠ (G.s : ℤ) - (e : ℤ) := by
      have : (i : ℤ) ≠ (e : ℤ) := by exact_mod_cast hie
      omega
    have hwi : (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) ≤ G.lbZ - 2 * G.v := by
      have h1 : (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1)
          ≤ (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        have : (G.sigma i : ℤ) ≤ (G.s : ℤ) := by exact_mod_cast hsigi.2
        linarith
      linarith
    have hwi0 : 0 ≤ (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1) := by
      refine mul_nonneg (by linarith) ?_
      have : (1 : ℤ) ≤ (G.sigma i : ℤ) := by exact_mod_cast hsigi.1
      linarith
    rcases G.bottom_out_strict (e := (G.s : ℤ) - (i : ℤ)) (f := (G.s : ℤ) - (e : ℤ))
      (w := (2 * (G.v : ℤ) - 1) * ((G.sigma i : ℤ) - 1)) (t := (G.v : ℤ)) hne hwi0 hwi
      (by linarith) (by linarith) with h | h <;> linarith

/-- A schematic satisfying the gap conditions respects the marks. -/
theorem respectsMarking_of_gapConditions (h : S.SatisfiesGapConditions G) :
    S.RespectsMarking G.marking := by
  obtain ⟨st, hGC⟩ := h
  exact
    { topArrowL := fun hi r x hx hgapL => respectsMarking_topArrowL hGC hi r x hx hgapL
      topArrowR := fun hi r x hx hgapR => respectsMarking_topArrowR hGC hi r x hx hgapR
      botArrowL := fun hi r x hx hgapL => respectsMarking_botArrowL hGC hi r x hx hgapL
      botArrowR := fun hi r x hx hgapR => respectsMarking_botArrowR hGC hi r x hx hgapR
      triangleR := fun i r x hx habove => respectsMarking_triangleR hGC i r x hx habove
      triangleL := fun i r x hx habove => respectsMarking_triangleL hGC i r x hx habove }

end Schematic

end StickPolyhex
