import Tiling.Proofs.ABLineValues

/-!
# From an index tiling to a gap assignment

This file proves the easy direction of Sections 2.6–2.8: if the data `D` built from a set of AB
tiles admits an index tiling, then the buckets `D.spec` admit a gap assignment.  The values are
the ones defined in `Tiling/Proofs/ABLineValues.lean`; what remains is to check, phase by phase,
that they satisfy the four conditions of a line assignment, which is what `IndexTiling.PhaseOK`
records.
-/

namespace StickPolyhex

namespace ABSim

namespace IndexTiling

variable {D : ABData} (T : IndexTiling D)

/-- The four gap conditions at the phase `j` of a cycle: the value of the line of the column `c`
and the value of the line to its right lie in the sets of the bucket `cur` of that phase, the two
lines move by opposite amounts, and the amount lies in the interval of the bucket `nxt` of the
next phase.  Which of the two lines is the "left" one alternates with the parity of the
phase. -/
def PhaseOK (c n : ℤ) (j : ℕ) (cur nxt : StateSpec) : Prop :=
  (j % 2 = 0 →
      T.xphase c n j ∈ cur.L ∧ T.yphase c n j ∈ cur.R ∧
      T.yphase c n (j + 1) - T.yphase c n j = -(T.xphase c n (j + 1) - T.xphase c n j) ∧
      nxt.lo ≤ T.xphase c n (j + 1) - T.xphase c n j ∧
        T.xphase c n (j + 1) - T.xphase c n j ≤ nxt.hi) ∧
  (j % 2 = 1 →
      T.xphase c n j ∈ cur.R ∧ T.yphase c n j ∈ cur.L ∧
      T.xphase (c + 1) n (j + 1) - T.xphase (c + 1) n j =
        -(T.yphase c n (j + 1) - T.yphase c n j) ∧
      nxt.lo ≤ T.yphase c n (j + 1) - T.yphase c n j ∧
        T.yphase c n (j + 1) - T.yphase c n j ≤ nxt.hi)

/-! ### Two general reductions -/

lemma phase_even {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {u u' e : ℤ} (hje : j % 2 = 0)
    (hx : T.xphase c n j = u) (hx1 : T.xphase c n (j + 1) = u')
    (hc : T.cphase c n j = e) (hc1 : T.cphase c n (j + 1) = e)
    (hL : u ∈ cur.L) (hR : D.vz - u + e ∈ cur.R)
    (hlo : nxt.lo ≤ u' - u) (hhi : u' - u ≤ nxt.hi) : T.PhaseOK c n j cur nxt := by
  refine ⟨fun _ => ⟨by rw [hx]; exact hL, ?_, ?_, ?_, ?_⟩, fun h => by omega⟩
  · unfold yphase; rw [hx, hc]; exact hR
  · unfold yphase; rw [hx, hx1, hc, hc1]; ring
  · rw [hx, hx1]; exact hlo
  · rw [hx, hx1]; exact hhi

lemma phase_odd {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {u u' w w' e e' : ℤ} (hjo : j % 2 = 1)
    (hx : T.xphase c n j = u) (hx1 : T.xphase c n (j + 1) = u')
    (hw : T.xphase (c + 1) n j = w) (hw1 : T.xphase (c + 1) n (j + 1) = w')
    (hc : T.cphase c n j = e) (hc1 : T.cphase c n (j + 1) = e')
    (hR : u ∈ cur.R) (hL : D.vz - u + e ∈ cur.L)
    (hpair : w' - w = -((D.vz - u' + e') - (D.vz - u + e)))
    (hlo : nxt.lo ≤ (D.vz - u' + e') - (D.vz - u + e))
    (hhi : (D.vz - u' + e') - (D.vz - u + e) ≤ nxt.hi) : T.PhaseOK c n j cur nxt := by
  refine ⟨fun h => by omega, fun _ => ⟨by rw [hx]; exact hR, ?_, ?_, ?_, ?_⟩⟩
  · unfold yphase; rw [hx, hc]; exact hL
  · unfold yphase; rw [hx, hx1, hc, hc1, hw, hw1]; exact hpair
  · unfold yphase; rw [hx, hx1, hc, hc1]; exact hlo
  · unfold yphase; rw [hx, hx1, hc, hc1]; exact hhi

/-! ### The four sub-phases of a matching gadget -/

lemma match_phase0 {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {g : ℤ → ℤ} {ℓ ℓ' : ℤ}
    (hje : j % 2 = 0) (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz)
    (hx : T.xphase c n j = D.mxv g ℓ 0) (hx1 : T.xphase c n (j + 1) = D.mxv g ℓ 1)
    (hc : T.cphase c n j = mcorr g ℓ ℓ' 0) (hc1 : T.cphase c n (j + 1) = mcorr g ℓ ℓ' 1)
    (hcL : cur.L = D.Eset) (hcR : cur.R = D.Eset)
    (hnlo : nxt.lo = 0) (hnhi : nxt.hi = 6 * D.kz) : T.PhaseOK c n j cur nxt := by
  have e0 := D.mxv_mem_Eset (g := g) (ℓ := ℓ) (i := 0) (Or.inl rfl) h1 h2
  have e1 := D.mxv_mem_Rload hgb h1 h2
  have hb := hgb ℓ
  have hzero : mcorr g ℓ ℓ' 0 = 0 := by unfold mcorr; norm_num
  have hzero1 : mcorr g ℓ ℓ' 1 = 0 := by unfold mcorr; norm_num
  rw [hzero] at hc
  rw [hzero1] at hc1
  refine T.phase_even hje hx hx1 hc hc1 ?_ ?_ ?_ ?_
  · rw [hcL]; exact e0.2.1
  · rw [hcR, add_zero]; exact e0.2.2
  · rw [hnlo, e0.1, e1.1]; omega
  · rw [hnhi, e0.1, e1.1]; omega

lemma match_phase1 {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {g : ℤ → ℤ} {ℓ ℓ' : ℤ}
    (hjo : j % 2 = 1) (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz) (h1' : 1 ≤ ℓ') (h2' : ℓ' ≤ 2 * D.tz)
    (hx : T.xphase c n j = D.mxv g ℓ 1) (hx1 : T.xphase c n (j + 1) = D.mxv g ℓ 2)
    (hw : T.xphase (c + 1) n j = D.mxv g ℓ' 1) (hw1 : T.xphase (c + 1) n (j + 1) = D.mxv g ℓ' 2)
    (hc : T.cphase c n j = mcorr g ℓ ℓ' 1) (hc1 : T.cphase c n (j + 1) = mcorr g ℓ ℓ' 2)
    (hcR : cur.R = D.Rload g) (hcL : cur.L = D.Efull)
    (hnlo : nxt.lo = 0) (hnhi : nxt.hi = 6 * D.kz) : T.PhaseOK c n j cur nxt := by
  have e1 := D.mxv_mem_Rload hgb h1 h2
  have e2 := D.mxv_mem_Eset (g := g) (ℓ := ℓ) (i := 2) (Or.inr (Or.inl rfl)) h1 h2
  have f1 := D.mxv_mem_Rload hgb h1' h2'
  have f2 := D.mxv_mem_Eset (g := g) (ℓ := ℓ') (i := 2) (Or.inr (Or.inl rfl)) h1' h2'
  have hb := hgb ℓ'
  have hzero : mcorr g ℓ ℓ' 1 = 0 := by unfold mcorr; norm_num
  have hcorr : mcorr g ℓ ℓ' 2 = g ℓ' - g ℓ := by unfold mcorr; norm_num
  rw [hzero] at hc
  rw [hcorr] at hc1
  refine T.phase_odd hjo hx hx1 hw hw1 hc hc1 ?_ ?_ ?_ ?_ ?_
  · rw [hcR]; exact e1.2.1
  · rw [hcL, add_zero]; exact e1.2.2
  · rw [e1.1, e2.1, f1.1, f2.1]; ring
  · rw [hnlo, e1.1, e2.1]; omega
  · rw [hnhi, e1.1, e2.1]; omega

lemma match_phase2 {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {g : ℤ → ℤ} {ℓ ℓ' : ℤ}
    (hje : j % 2 = 0) (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz)
    (hx : T.xphase c n j = D.mxv g ℓ 2) (hx1 : T.xphase c n (j + 1) = D.mxv g ℓ 3)
    (hc : T.cphase c n j = mcorr g ℓ ℓ' 2) (hc1 : T.cphase c n (j + 1) = mcorr g ℓ ℓ' 3)
    (hcL : cur.L = D.Eset) (hAset : D.vz - D.d * ℓ + (g ℓ' - g ℓ) ∈ cur.R)
    (hnlo : nxt.lo = 0) (hnhi : nxt.hi = 6 * D.kz) : T.PhaseOK c n j cur nxt := by
  have e2 := D.mxv_mem_Eset (g := g) (ℓ := ℓ) (i := 2) (Or.inr (Or.inl rfl)) h1 h2
  have e3 := D.mxv_mem_Rreset (g := g) hgb h1 h2
  have hb := hgb ℓ
  have hcorr : mcorr g ℓ ℓ' 2 = g ℓ' - g ℓ := by unfold mcorr; norm_num
  have hcorr' : mcorr g ℓ ℓ' 3 = g ℓ' - g ℓ := by unfold mcorr; norm_num
  rw [hcorr] at hc
  rw [hcorr'] at hc1
  refine T.phase_even hje hx hx1 hc hc1 ?_ ?_ ?_ ?_
  · rw [hcL]; exact e2.2.1
  · rw [e2.1]; exact hAset
  · rw [hnlo, e2.1, e3.1]; omega
  · rw [hnhi, e2.1, e3.1]; omega

lemma match_phase3 {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {g : ℤ → ℤ} {ℓ ℓ' : ℤ}
    (hjo : j % 2 = 1) (hgb : ∀ x, 2 * D.kz ≤ g x ∧ g x ≤ 5 * D.kz - 1)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 2 * D.tz) (h1' : 1 ≤ ℓ') (h2' : ℓ' ≤ 2 * D.tz)
    (hx : T.xphase c n j = D.mxv g ℓ 3) (hx1 : T.xphase c n (j + 1) = D.mxv g ℓ 4)
    (hw : T.xphase (c + 1) n j = D.mxv g ℓ' 3) (hw1 : T.xphase (c + 1) n (j + 1) = D.mxv g ℓ' 4)
    (hc : T.cphase c n j = mcorr g ℓ ℓ' 3) (hc1 : T.cphase c n (j + 1) = mcorr g ℓ ℓ' 4)
    (hcR : cur.R = D.Rreset) (hcL : cur.L = D.Efull)
    (hnlo : nxt.lo = 0) (hnhi : nxt.hi = 6 * D.kz) : T.PhaseOK c n j cur nxt := by
  have hk := D.one_le_kz
  have e3 := D.mxv_mem_Rreset (g := g) hgb h1 h2
  have e4 := D.mxv_mem_Eset (g := g) (ℓ := ℓ) (i := 4) (Or.inr (Or.inr rfl)) h1 h2
  have f3 := D.mxv_mem_Rreset (g := g) hgb h1' h2'
  have f4 := D.mxv_mem_Eset (g := g) (ℓ := ℓ') (i := 4) (Or.inr (Or.inr rfl)) h1' h2'
  have hb := hgb ℓ
  have hb' := hgb ℓ'
  have hcorr : mcorr g ℓ ℓ' 3 = g ℓ' - g ℓ := by unfold mcorr; norm_num
  have hcorr' : mcorr g ℓ ℓ' 4 = 0 := by unfold mcorr; norm_num
  rw [hcorr] at hc
  rw [hcorr'] at hc1
  refine T.phase_odd hjo hx hx1 hw hw1 hc hc1 ?_ ?_ ?_ ?_ ?_
  · rw [hcR]; exact e3.2
  · rw [hcL, e3.1]
    have hval : D.vz - (D.d * ℓ + 6 * D.kz - g ℓ) + (g ℓ' - g ℓ) =
        D.d * (2 * D.tz + 1 - ℓ) + (g ℓ' - 6 * D.kz) := by
      rw [D.vz_eq]; ring
    rw [hval]
    exact (D.slot_mem_Efull (by omega) (by omega) (by omega) (by omega)).1
  · rw [e3.1, e4.1, f3.1, f4.1]; ring
  · rw [hnlo, e3.1, e4.1]; omega
  · rw [hnhi, e3.1, e4.1]; omega

/-! ### The phases of a free gadget -/

lemma free_odd {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {u w : ℤ} (hjo : j % 2 = 1)
    (hx : T.xphase c n j = u) (hx1 : T.xphase c n (j + 1) = u)
    (hw : T.xphase (c + 1) n j = w) (hw1 : T.xphase (c + 1) n (j + 1) = w)
    (hc : T.cphase c n j = 0) (hc1 : T.cphase c n (j + 1) = 0)
    (hR : u ∈ cur.R) (hL : D.vz - u ∈ cur.L) (hnlo : nxt.lo = 0) (hnhi : nxt.hi = 0) :
    T.PhaseOK c n j cur nxt := by
  refine T.phase_odd hjo hx hx1 hw hw1 hc hc1 hR ?_ ?_ ?_ ?_
  · rw [add_zero]; exact hL
  · ring
  · rw [hnlo]; omega
  · rw [hnhi]; omega

lemma free_even {c n : ℤ} {j : ℕ} {cur nxt : StateSpec} {u u' : ℤ} (hje : j % 2 = 0)
    (hx : T.xphase c n j = u) (hx1 : T.xphase c n (j + 1) = u')
    (hc : T.cphase c n j = 0) (hc1 : T.cphase c n (j + 1) = 0)
    (hL : u ∈ cur.L) (hR : D.vz - u ∈ cur.R)
    (hlo : nxt.lo ≤ u' - u) (hhi : u' - u ≤ nxt.hi) : T.PhaseOK c n j cur nxt :=
  T.phase_even hje hx hx1 hc hc1 hL (by rw [add_zero]; exact hR) hlo hhi

/-! ### The alternation of the indices of two adjacent columns -/

lemma alt₁ (c n : ℤ) :
    (T.ix c n ≤ D.tz ∧ ¬ T.ix (c + 1) n ≤ D.tz ∧ D.h₁ (T.ix c n) = D.h₁ (T.ix (c + 1) n)) ∨
      (¬ T.ix c n ≤ D.tz ∧ T.ix (c + 1) n ≤ D.tz) := by
  by_cases hc : c % 2 = 0
  · exact Or.inl ⟨T.ix_A c n hc, by have := T.ix_B (c + 1) n (by omega); omega,
      T.match1 c n (Int.even_iff.2 hc)⟩
  · exact Or.inr ⟨by have := T.ix_B c n hc; omega, T.ix_A (c + 1) n (by omega)⟩

lemma alt₂ (c n : ℤ) :
    (T.ix c n ≤ D.tz ∧ ¬ T.ix (c + 1) n ≤ D.tz) ∨
      (¬ T.ix c n ≤ D.tz ∧ T.ix (c + 1) n ≤ D.tz ∧ D.h₂ (T.ix c n) = D.h₂ (T.ix (c + 1) n)) := by
  by_cases hc : c % 2 = 0
  · exact Or.inl ⟨T.ix_A c n hc, by have := T.ix_B (c + 1) n (by omega); omega⟩
  · exact Or.inr ⟨by have := T.ix_B c n hc; omega, T.ix_A (c + 1) n (by omega),
      T.match2 c n (fun he => hc (Int.even_iff.1 he))⟩

lemma alt₃ (c n : ℤ) :
    (T.jx c n ≤ D.tz ∧ ¬ T.jx (c + 1) n ≤ D.tz ∧ D.h₃ (T.jx c n) = D.h₃ (T.jx (c + 1) n)) ∨
      (¬ T.jx c n ≤ D.tz ∧ T.jx (c + 1) n ≤ D.tz) := by
  by_cases hc : c % 2 = 0
  · exact Or.inl ⟨T.jx_A c n hc, by have := T.jx_B (c + 1) n (by omega); omega,
      T.match3 c n (Int.even_iff.2 hc)⟩
  · exact Or.inr ⟨by have := T.jx_B c n hc; omega, T.jx_A (c + 1) n (by omega)⟩

lemma alt₄ (c n : ℤ) :
    (T.jx c n ≤ D.tz ∧ ¬ T.jx (c + 1) n ≤ D.tz) ∨
      (¬ T.jx c n ≤ D.tz ∧ T.jx (c + 1) n ≤ D.tz ∧ D.h₄ (T.jx c n) = D.h₄ (T.jx (c + 1) n)) := by
  by_cases hc : c % 2 = 0
  · exact Or.inl ⟨T.jx_A c n hc, by have := T.jx_B (c + 1) n (by omega); omega⟩
  · exact Or.inr ⟨by have := T.jx_B c n hc; omega, T.jx_A (c + 1) n (by omega),
      T.match4 c n (fun he => hc (Int.even_iff.1 he))⟩

/-! ### The first two matching gadgets -/

lemma phaseOK_0 (c n : ℤ) : T.PhaseOK c n 0 (D.data 1) (D.data 2) :=
  T.match_phase0 (g := D.g₁) (ℓ' := T.ix (c + 1) n) (by omega) D.g₁_bounds
    (T.ix_one_le c n) (T.ix_le c n) (T.xphase_m1 c n 0 (by omega)) (T.xphase_m1 c n 1 (by omega))
    (T.cphase_m1 c n 0 (by omega)) (T.cphase_m1 c n 1 (by omega)) rfl rfl rfl rfl

lemma phaseOK_1 (c n : ℤ) : T.PhaseOK c n 1 (D.data 2) (D.data 3) :=
  T.match_phase1 (g := D.g₁) (by omega) D.g₁_bounds
    (T.ix_one_le c n) (T.ix_le c n) (T.ix_one_le (c + 1) n) (T.ix_le (c + 1) n)
    (T.xphase_m1 c n 1 (by omega)) (T.xphase_m1 c n 2 (by omega))
    (T.xphase_m1 (c + 1) n 1 (by omega)) (T.xphase_m1 (c + 1) n 2 (by omega))
    (T.cphase_m1 c n 1 (by omega)) (T.cphase_m1 c n 2 (by omega)) rfl rfl rfl rfl

lemma phaseOK_2 (c n : ℤ) : T.PhaseOK c n 2 (D.data 3) (D.data 4) := by
  refine T.match_phase2 (g := D.g₁) (ℓ' := T.ix (c + 1) n) (by omega) D.g₁_bounds
    (T.ix_one_le c n) (T.ix_le c n) (T.xphase_m1 c n 2 (by omega)) (T.xphase_m1 c n 3 (by omega))
    (T.cphase_m1 c n 2 (by omega)) (T.cphase_m1 c n 3 (by omega)) rfl ?_ rfl rfl
  exact D.Aset_of_match D.h₁_lt D.g₁_eq (T.ix_one_le c n) (T.ix_le c n) (T.alt₁ c n)

lemma phaseOK_3 (c n : ℤ) : T.PhaseOK c n 3 (D.data 4) (D.data 5) :=
  T.match_phase3 (g := D.g₁) (by omega) D.g₁_bounds
    (T.ix_one_le c n) (T.ix_le c n) (T.ix_one_le (c + 1) n) (T.ix_le (c + 1) n)
    (T.xphase_m1 c n 3 (by omega)) (T.xphase_m1 c n 4 (by omega))
    (T.xphase_m1 (c + 1) n 3 (by omega)) (T.xphase_m1 (c + 1) n 4 (by omega))
    (T.cphase_m1 c n 3 (by omega)) (T.cphase_m1 c n 4 (by omega)) rfl rfl rfl rfl

lemma phaseOK_4 (c n : ℤ) : T.PhaseOK c n 4 (D.data 5) (D.data 6) := by
  refine T.match_phase0 (g := D.g₂) (ℓ' := T.ix (c + 1) n) (by omega) D.g₂_bounds
    (T.ix_one_le c n) (T.ix_le c n) ?_ (T.xphase_m2 c n 1 (by omega) (by omega))
    ?_ (T.cphase_m2 c n 1 (by omega) (by omega)) rfl rfl rfl rfl
  · rw [T.xphase_m1 c n 4 (by omega), D.mxv_four, D.mxv_zero]
  · rw [T.cphase_m1 c n 4 (by omega)]; unfold mcorr; norm_num

lemma phaseOK_5 (c n : ℤ) : T.PhaseOK c n 5 (D.data 6) (D.data 7) :=
  T.match_phase1 (g := D.g₂) (by omega) D.g₂_bounds
    (T.ix_one_le c n) (T.ix_le c n) (T.ix_one_le (c + 1) n) (T.ix_le (c + 1) n)
    (T.xphase_m2 c n 1 (by omega) (by omega)) (T.xphase_m2 c n 2 (by omega) (by omega))
    (T.xphase_m2 (c + 1) n 1 (by omega) (by omega))
    (T.xphase_m2 (c + 1) n 2 (by omega) (by omega))
    (T.cphase_m2 c n 1 (by omega) (by omega)) (T.cphase_m2 c n 2 (by omega) (by omega))
    rfl rfl rfl rfl

lemma phaseOK_6 (c n : ℤ) : T.PhaseOK c n 6 (D.data 7) (D.data 8) := by
  refine T.match_phase2 (g := D.g₂) (ℓ' := T.ix (c + 1) n) (by omega) D.g₂_bounds
    (T.ix_one_le c n) (T.ix_le c n) (T.xphase_m2 c n 2 (by omega) (by omega))
    (T.xphase_m2 c n 3 (by omega) (by omega))
    (T.cphase_m2 c n 2 (by omega) (by omega)) (T.cphase_m2 c n 3 (by omega) (by omega))
    rfl ?_ rfl rfl
  exact D.Aset_of_match' D.h₂_lt D.g₂_eq (T.ix_one_le c n) (T.ix_le c n) (T.alt₂ c n)

lemma phaseOK_7 (c n : ℤ) : T.PhaseOK c n 7 (D.data 8) (D.data 9) :=
  T.match_phase3 (g := D.g₂) (by omega) D.g₂_bounds
    (T.ix_one_le c n) (T.ix_le c n) (T.ix_one_le (c + 1) n) (T.ix_le (c + 1) n)
    (T.xphase_m2 c n 3 (by omega) (by omega)) (T.xphase_m2 c n 4 (by omega) (by omega))
    (T.xphase_m2 (c + 1) n 3 (by omega) (by omega))
    (T.xphase_m2 (c + 1) n 4 (by omega) (by omega))
    (T.cphase_m2 c n 3 (by omega) (by omega)) (T.cphase_m2 c n 4 (by omega) (by omega))
    rfl rfl rfl rfl

/-! ### The first free gadget -/

lemma phaseOK_8 (c n : ℤ) : T.PhaseOK c n 8 (D.data 9) (D.data 10) := by
  have hP := D.one_le_P
  have hlo := T.ix_one_le c n
  have hhi := T.ix_le c n
  have hB := T.ix_B c n
  have hnxt : D.data 10 = ⟨D.Efull, D.C₁ 1, -D.d + 1, 1⟩ := by
    have h1 := D.data_f1 1 (by omega) (by omega)
    have h2 := D.freeData₁_odd 1 (by omega) hP
    norm_num at h1 h2
    rw [h1, h2]
  have h9 : T.xphase c n 9 = D.comp1 c (T.ix c n) 1 := by
    have h := T.xphase_c1_odd c n 1 (by omega) hP
    norm_num at h
    exact h
  have hstep := D.comp1_step (c := c) (ℓ := T.ix c n) (p := 0) hB
  rw [D.comp1_zero hB] at hstep
  simp only [zero_add] at hstep
  have e0 := D.mxv_mem_Eset (g := D.g₂) (ℓ := T.ix c n) (i := 4) (Or.inr (Or.inr rfl)) hlo hhi
  rw [hnxt]
  refine T.free_even (u := D.d * T.ix c n) (u' := D.comp1 c (T.ix c n) 1) (by omega) ?_ h9
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [T.xphase_m2 c n 4 (by omega) (by omega), D.mxv_four]
  · rw [T.cphase_m2 c n 4 (by omega) (by omega)]; unfold mcorr; norm_num
  · exact T.cphase_free1 c n 9 (by omega) (by omega)
  · rw [← D.mxv_four D.g₂ (T.ix c n)]; exact e0.2.1
  · rw [← D.mxv_four D.g₂ (T.ix c n)]; exact e0.2.2
  · exact hstep.1
  · exact hstep.2

lemma phaseOK_c1_odd (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ D.P) :
    T.PhaseOK c n (7 + 2 * p) (D.data (8 + 2 * p)) (D.data (9 + 2 * p)) := by
  have hpb := D.pz_bound hp2
  have hcur : D.data (8 + 2 * p) = ⟨D.Efull, D.C₁ (p : ℤ), -D.d + 1, 1⟩ := by
    rw [show 8 + 2 * p = 9 + (2 * p - 1) by omega, D.data_f1 (2 * p - 1) (by omega) (by omega),
      D.freeData₁_odd p hp1 hp2]
  have hnxt : D.data (9 + 2 * p) = ⟨D.C₁ (p : ℤ), D.Efull, 0, 0⟩ := by
    rw [D.data_f1 (2 * p) (by omega) (by omega), D.freeData₁_even p hp2]
  have hm := D.comp1_mem (c := c) (ℓ := T.ix c n) (p := (p : ℤ)) (T.ix_one_le c n) (T.ix_le c n)
    (T.ix_A c n) (T.ix_B c n) hpb.1 hpb.2
  rw [hcur, hnxt]
  exact T.free_odd (by omega) (T.xphase_c1_odd c n p hp1 hp2)
    (by rw [show 7 + 2 * p + 1 = 8 + 2 * p by omega]; exact T.xphase_c1_even c n p hp1 hp2)
    (T.xphase_c1_odd (c + 1) n p hp1 hp2)
    (by rw [show 7 + 2 * p + 1 = 8 + 2 * p by omega]; exact T.xphase_c1_even (c + 1) n p hp1 hp2)
    (T.cphase_free1 c n (7 + 2 * p) (by omega) (by omega))
    (T.cphase_free1 c n (7 + 2 * p + 1) (by omega) (by omega)) hm.1 hm.2.2 rfl rfl

lemma phaseOK_c1_even (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p < D.P) :
    T.PhaseOK c n (8 + 2 * p) (D.data (9 + 2 * p)) (D.data (10 + 2 * p)) := by
  have hpb := D.pz_bound (le_of_lt hp2)
  have hcur : D.data (9 + 2 * p) = ⟨D.C₁ (p : ℤ), D.Efull, 0, 0⟩ := by
    rw [D.data_f1 (2 * p) (by omega) (by omega), D.freeData₁_even p (by omega)]
  have hnxt : D.data (10 + 2 * p) = ⟨D.Efull, D.C₁ ((p : ℤ) + 1), -D.d + 1, 1⟩ := by
    rw [show 10 + 2 * p = 9 + (2 * (p + 1) - 1) by omega,
      D.data_f1 (2 * (p + 1) - 1) (by omega) (by omega), D.freeData₁_odd (p + 1) (by omega)
      (by omega)]
    norm_num
  have hm := D.comp1_mem (c := c) (ℓ := T.ix c n) (p := (p : ℤ)) (T.ix_one_le c n) (T.ix_le c n)
    (T.ix_A c n) (T.ix_B c n) hpb.1 hpb.2
  have hstep := D.comp1_step (c := c) (ℓ := T.ix c n) (p := (p : ℤ)) (T.ix_B c n)
  rw [hcur, hnxt]
  refine T.free_even (u := D.comp1 c (T.ix c n) (p : ℤ))
    (u' := D.comp1 c (T.ix c n) ((p : ℤ) + 1)) (by omega)
    (T.xphase_c1_even c n p hp1 (by omega)) ?_
    (T.cphase_free1 c n (8 + 2 * p) (by omega) (by omega))
    (T.cphase_free1 c n (8 + 2 * p + 1) (by omega) (by omega)) hm.1 hm.2.2 hstep.1 hstep.2
  have h := T.xphase_c1_odd c n (p + 1) (by omega) (by omega)
  rw [show 8 + 2 * p + 1 = 7 + 2 * (p + 1) by omega]
  rw [h]
  norm_num

lemma phaseOK_c1_mid (c n : ℤ) :
    T.PhaseOK c n (8 + 2 * D.P) (D.data (9 + 2 * D.P)) (D.data (10 + 2 * D.P)) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound (le_refl D.P)
  have hcur : D.data (9 + 2 * D.P) = ⟨D.C₁ (D.P : ℤ), D.Efull, 0, 0⟩ := by
    rw [D.data_f1 (2 * D.P) (by omega) (by omega), D.freeData₁_even D.P (by omega)]
  have hnxt : D.data (10 + 2 * D.P) = ⟨D.Efull, D.D₁ 1, -1, D.d - 1⟩ := by
    have h2 := D.freeData₁_exp_odd 1 (by omega)
    norm_num at h2
    rw [show 10 + 2 * D.P = 9 + (2 * D.P + 1) by omega,
      D.data_f1 (2 * D.P + 1) (by omega) (by omega), h2]
  have hm := D.comp1_mem (c := c) (ℓ := T.ix c n) (p := (D.P : ℤ)) (T.ix_one_le c n)
    (T.ix_le c n) (T.ix_A c n) (T.ix_B c n) hpb.1 hpb.2
  have hstep := D.comp1_exp1_step (c := c) (ℓ := T.ix c n) (L := T.jx c n) (T.ix_B c n)
    (T.jx_B c n) (fun h => T.lockA' c n h) (T.ix_le c n)
  rw [hcur, hnxt]
  rw [D.pz_cast] at hm
  refine T.free_even (u := D.comp1 c (T.ix c n) D.pz) (u' := D.exp1 c (T.jx c n) 1) (by omega)
    ?_ ?_ (T.cphase_free1 c n (8 + 2 * D.P) (by omega) (by omega))
    (T.cphase_free1 c n (8 + 2 * D.P + 1) (by omega) (by omega)) hm.1 hm.2.2 hstep.1 hstep.2
  · rw [← D.pz_cast]; exact T.xphase_c1_even c n D.P (by omega) (by omega)
  · have h := T.xphase_e1_odd c n 1 (by omega) hP
    rw [show 8 + 2 * D.P + 1 = 7 + 2 * D.P + 2 * 1 by omega, h]
    norm_num

lemma phaseOK_e1_odd (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ D.P) :
    T.PhaseOK c n (7 + 2 * D.P + 2 * p) (D.data (8 + 2 * D.P + 2 * p))
      (D.data (9 + 2 * D.P + 2 * p)) := by
  have hpb := D.pz_bound hp2
  have hcur : D.data (8 + 2 * D.P + 2 * p) = ⟨D.Efull, D.D₁ (p : ℤ), -1, D.d - 1⟩ := by
    rw [show 8 + 2 * D.P + 2 * p = 9 + (2 * D.P + 2 * p - 1) by omega,
      D.data_f1 (2 * D.P + 2 * p - 1) (by omega) (by omega), D.freeData₁_exp_odd p hp1]
  have hnxtlo : (D.data (9 + 2 * D.P + 2 * p)).lo = 0 ∧
      (D.data (9 + 2 * D.P + 2 * p)).hi = 0 := by
    rw [show 9 + 2 * D.P + 2 * p = 9 + (2 * D.P + 2 * p) by omega,
      D.data_f1 (2 * D.P + 2 * p) (by omega) (by omega)]
    by_cases hlt : p = D.P
    · rw [hlt, show 2 * D.P + 2 * D.P = 4 * D.P by omega, D.freeData₁_last]
      exact ⟨rfl, rfl⟩
    · rw [D.freeData₁_exp_even p hp1 (by omega)]
      exact ⟨rfl, rfl⟩
  have hm := D.exp1_mem (c := c) (L := T.jx c n) (p := (p : ℤ)) (T.jx_one_le c n) (T.jx_le c n)
    (T.jx_A c n) (T.jx_B c n) hpb.1 hpb.2
  rw [hcur]
  exact T.free_odd (by omega) (T.xphase_e1_odd c n p hp1 hp2)
    (by rw [show 7 + 2 * D.P + 2 * p + 1 = 8 + 2 * D.P + 2 * p by omega]
        exact T.xphase_e1_even c n p hp1 hp2)
    (T.xphase_e1_odd (c + 1) n p hp1 hp2)
    (by rw [show 7 + 2 * D.P + 2 * p + 1 = 8 + 2 * D.P + 2 * p by omega]
        exact T.xphase_e1_even (c + 1) n p hp1 hp2)
    (T.cphase_free1 c n (7 + 2 * D.P + 2 * p) (by omega) (by omega))
    (T.cphase_free1 c n (7 + 2 * D.P + 2 * p + 1) (by omega) (by omega)) hm.1 hm.2.2
    hnxtlo.1 hnxtlo.2

lemma phaseOK_e1_even (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p < D.P) :
    T.PhaseOK c n (8 + 2 * D.P + 2 * p) (D.data (9 + 2 * D.P + 2 * p))
      (D.data (10 + 2 * D.P + 2 * p)) := by
  have hpb := D.pz_bound (le_of_lt hp2)
  have hcur : D.data (9 + 2 * D.P + 2 * p) = ⟨D.D₁ (p : ℤ), D.Efull, 0, 0⟩ := by
    rw [show 9 + 2 * D.P + 2 * p = 9 + (2 * D.P + 2 * p) by omega,
      D.data_f1 (2 * D.P + 2 * p) (by omega) (by omega),
      D.freeData₁_exp_even p hp1 (by omega)]
  have hnxt : D.data (10 + 2 * D.P + 2 * p) = ⟨D.Efull, D.D₁ ((p : ℤ) + 1), -1, D.d - 1⟩ := by
    have h2 := D.freeData₁_exp_odd (p + 1) (by omega)
    rw [show 10 + 2 * D.P + 2 * p = 9 + (2 * D.P + 2 * (p + 1) - 1) by omega,
      D.data_f1 (2 * D.P + 2 * (p + 1) - 1) (by omega) (by omega), h2]
    norm_num
  have hm := D.exp1_mem (c := c) (L := T.jx c n) (p := (p : ℤ)) (T.jx_one_le c n) (T.jx_le c n)
    (T.jx_A c n) (T.jx_B c n) hpb.1 hpb.2
  have hstep := D.exp1_step (c := c) (L := T.jx c n) (p := (p : ℤ))
  rw [hcur, hnxt]
  refine T.free_even (u := D.exp1 c (T.jx c n) (p : ℤ))
    (u' := D.exp1 c (T.jx c n) ((p : ℤ) + 1)) (by omega)
    (T.xphase_e1_even c n p hp1 (by omega)) ?_
    (T.cphase_free1 c n (8 + 2 * D.P + 2 * p) (by omega) (by omega))
    (T.cphase_free1 c n (8 + 2 * D.P + 2 * p + 1) (by omega) (by omega)) hm.1 hm.2.2
    hstep.1 hstep.2
  have h := T.xphase_e1_odd c n (p + 1) (by omega) (by omega)
  rw [show 8 + 2 * D.P + 2 * p + 1 = 7 + 2 * D.P + 2 * (p + 1) by omega, h]
  norm_num

/-! ### The last two matching gadgets -/

lemma data_N1 : D.data (8 + 4 * D.P + 1) = ⟨D.D₁ (D.P : ℤ), D.Eset, 0, 0⟩ := by
  have hP := D.one_le_P
  rw [show 8 + 4 * D.P + 1 = 9 + 4 * D.P by omega, D.data_f1 (4 * D.P) (by omega) (by omega),
    D.freeData₁_last]

lemma data_m3' (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    D.data (8 + 4 * D.P + i + 1) = D.matchData D.g₃ i := by
  rw [show 8 + 4 * D.P + i + 1 = 9 + 4 * D.P + i by omega]
  exact D.data_m3 i h1 h2

lemma data_m4' (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    D.data (8 + 4 * D.P + 4 + i + 1) = D.matchData D.g₄ i := by
  rw [show 8 + 4 * D.P + 4 + i + 1 = 13 + 4 * D.P + i by omega]
  exact D.data_m4 i h1 h2

lemma xphase_start3 (c n : ℤ) : T.xphase c n (8 + 4 * D.P) = D.mxv D.g₃ (T.jx c n) 0 := by
  have hP := D.one_le_P
  have h := T.xphase_e1_even c n D.P (by omega) (by omega)
  rw [show 8 + 4 * D.P = 8 + 2 * D.P + 2 * D.P by omega, h, D.pz_cast,
    D.exp1_top (T.jx_le c n), D.mxv_zero]

lemma phaseOK_N (c n : ℤ) :
    T.PhaseOK c n (8 + 4 * D.P) (D.data (8 + 4 * D.P + 1)) (D.data (8 + 4 * D.P + 1 + 1)) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound (le_refl D.P)
  have hcur := data_N1 (D := D)
  have hnxt : D.data (8 + 4 * D.P + 1 + 1) = D.matchData D.g₃ 1 := by
    rw [show 8 + 4 * D.P + 1 + 1 = 8 + 4 * D.P + 1 + 1 from rfl]
    exact data_m3' (D := D) 1 (by omega) (by omega)
  refine T.match_phase0 (g := D.g₃) (ℓ := T.jx c n) (ℓ' := T.jx (c + 1) n) (by omega)
    D.g₃_bounds (T.jx_one_le c n) (T.jx_le c n) (T.xphase_start3 c n) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [show 8 + 4 * D.P + 1 = 8 + 4 * D.P + 1 from rfl]
    exact T.xphase_m3 c n 1 (by omega) (by omega)
  · rw [T.cphase_free1 c n (8 + 4 * D.P) (by omega) (by omega)]; unfold mcorr; norm_num
  · rw [show 8 + 4 * D.P + 1 = 8 + 4 * D.P + 1 from rfl,
      T.cphase_m3 c n 1 (by omega) (by omega)]
  · rw [hcur]
    show D.D₁ (D.P : ℤ) = D.Eset
    rw [D.pz_cast]; exact D.D₁_top
  · rw [hcur]
  · rw [hnxt]; rfl
  · rw [hnxt]; rfl

lemma phaseOK_N1 (c n : ℤ) :
    T.PhaseOK c n (8 + 4 * D.P + 1) (D.data (8 + 4 * D.P + 1 + 1))
      (D.data (8 + 4 * D.P + 1 + 1 + 1)) := by
  have hc1 : D.data (8 + 4 * D.P + 1 + 1) = D.matchData D.g₃ 1 := data_m3' (D := D) 1 (by omega) (by omega)
  have hc2 : D.data (8 + 4 * D.P + 1 + 1 + 1) = D.matchData D.g₃ 2 := by
    rw [show 8 + 4 * D.P + 1 + 1 + 1 = 8 + 4 * D.P + 2 + 1 by omega]
    exact data_m3' (D := D) 2 (by omega) (by omega)
  rw [hc1, hc2]
  exact T.match_phase1 (g := D.g₃) (by omega) D.g₃_bounds
    (T.jx_one_le c n) (T.jx_le c n) (T.jx_one_le (c + 1) n) (T.jx_le (c + 1) n)
    (T.xphase_m3 c n 1 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 1 + 1 = 8 + 4 * D.P + 2 by omega]
        exact T.xphase_m3 c n 2 (by omega) (by omega))
    (T.xphase_m3 (c + 1) n 1 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 1 + 1 = 8 + 4 * D.P + 2 by omega]
        exact T.xphase_m3 (c + 1) n 2 (by omega) (by omega))
    (T.cphase_m3 c n 1 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 1 + 1 = 8 + 4 * D.P + 2 by omega]
        exact T.cphase_m3 c n 2 (by omega) (by omega)) rfl rfl rfl rfl

lemma phaseOK_N2 (c n : ℤ) :
    T.PhaseOK c n (8 + 4 * D.P + 2) (D.data (8 + 4 * D.P + 2 + 1))
      (D.data (8 + 4 * D.P + 2 + 1 + 1)) := by
  have hc1 : D.data (8 + 4 * D.P + 2 + 1) = D.matchData D.g₃ 2 := data_m3' (D := D) 2 (by omega) (by omega)
  have hc2 : D.data (8 + 4 * D.P + 2 + 1 + 1) = D.matchData D.g₃ 3 := by
    rw [show 8 + 4 * D.P + 2 + 1 + 1 = 8 + 4 * D.P + 3 + 1 by omega]
    exact data_m3' (D := D) 3 (by omega) (by omega)
  rw [hc1, hc2]
  refine T.match_phase2 (g := D.g₃) (ℓ' := T.jx (c + 1) n) (by omega) D.g₃_bounds
    (T.jx_one_le c n) (T.jx_le c n) (T.xphase_m3 c n 2 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 2 + 1 = 8 + 4 * D.P + 3 by omega]
        exact T.xphase_m3 c n 3 (by omega) (by omega))
    (T.cphase_m3 c n 2 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 2 + 1 = 8 + 4 * D.P + 3 by omega]
        exact T.cphase_m3 c n 3 (by omega) (by omega)) rfl ?_ rfl rfl
  exact D.Aset_of_match D.h₃_lt D.g₃_eq (T.jx_one_le c n) (T.jx_le c n) (T.alt₃ c n)

lemma phaseOK_N3 (c n : ℤ) :
    T.PhaseOK c n (8 + 4 * D.P + 3) (D.data (8 + 4 * D.P + 3 + 1))
      (D.data (8 + 4 * D.P + 3 + 1 + 1)) := by
  have hc1 : D.data (8 + 4 * D.P + 3 + 1) = D.matchData D.g₃ 3 := data_m3' (D := D) 3 (by omega) (by omega)
  have hc2 : D.data (8 + 4 * D.P + 3 + 1 + 1) = D.matchData D.g₃ 4 := by
    rw [show 8 + 4 * D.P + 3 + 1 + 1 = 8 + 4 * D.P + 4 + 1 by omega]
    exact data_m3' (D := D) 4 (by omega) (by omega)
  rw [hc1, hc2]
  exact T.match_phase3 (g := D.g₃) (by omega) D.g₃_bounds
    (T.jx_one_le c n) (T.jx_le c n) (T.jx_one_le (c + 1) n) (T.jx_le (c + 1) n)
    (T.xphase_m3 c n 3 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 3 + 1 = 8 + 4 * D.P + 4 by omega]
        exact T.xphase_m3 c n 4 (by omega) (by omega))
    (T.xphase_m3 (c + 1) n 3 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 3 + 1 = 8 + 4 * D.P + 4 by omega]
        exact T.xphase_m3 (c + 1) n 4 (by omega) (by omega))
    (T.cphase_m3 c n 3 (by omega) (by omega))
    (by rw [show 8 + 4 * D.P + 3 + 1 = 8 + 4 * D.P + 4 by omega]
        exact T.cphase_m3 c n 4 (by omega) (by omega)) rfl rfl rfl rfl

lemma phaseOK_N4 (c n : ℤ) :
    T.PhaseOK c n (8 + 4 * D.P + 4) (D.data (8 + 4 * D.P + 4 + 1))
      (D.data (8 + 4 * D.P + 4 + 1 + 1)) := by
  have hc1 : D.data (8 + 4 * D.P + 4 + 1) = D.matchData D.g₃ 4 := data_m3' (D := D) 4 (by omega) (by omega)
  have hc2 : D.data (8 + 4 * D.P + 4 + 1 + 1) = D.matchData D.g₄ 1 := by
    rw [show 8 + 4 * D.P + 4 + 1 + 1 = 8 + 4 * D.P + 4 + 1 + 1 from rfl]
    exact data_m4' (D := D) 1 (by omega) (by omega)
  rw [hc1, hc2]
  refine T.match_phase0 (g := D.g₄) (ℓ := T.jx c n) (ℓ' := T.jx (c + 1) n) (by omega)
    D.g₄_bounds (T.jx_one_le c n) (T.jx_le c n) ?_ ?_ ?_ ?_ rfl rfl rfl rfl
  · rw [T.xphase_m3 c n 4 (by omega) (by omega), D.mxv_four, D.mxv_zero]
  · rw [show 8 + 4 * D.P + 4 + 1 = 12 + 4 * D.P + 1 by omega]
    exact T.xphase_m4 c n 1 (by omega) (by omega)
  · rw [T.cphase_m3 c n 4 (by omega) (by omega)]; unfold mcorr; norm_num
  · rw [show 8 + 4 * D.P + 4 + 1 = 12 + 4 * D.P + 1 by omega]
    exact T.cphase_m4 c n 1 (by omega) (by omega)

lemma phaseOK_N5 (c n : ℤ) :
    T.PhaseOK c n (12 + 4 * D.P + 1) (D.data (12 + 4 * D.P + 1 + 1))
      (D.data (12 + 4 * D.P + 1 + 1 + 1)) := by
  have hc1 : D.data (12 + 4 * D.P + 1 + 1) = D.matchData D.g₄ 1 := by
    rw [show 12 + 4 * D.P + 1 + 1 = 13 + 4 * D.P + 1 by omega]
    exact D.data_m4 1 (by omega) (by omega)
  have hc2 : D.data (12 + 4 * D.P + 1 + 1 + 1) = D.matchData D.g₄ 2 := by
    rw [show 12 + 4 * D.P + 1 + 1 + 1 = 13 + 4 * D.P + 2 by omega]
    exact D.data_m4 2 (by omega) (by omega)
  rw [hc1, hc2]
  exact T.match_phase1 (g := D.g₄) (by omega) D.g₄_bounds
    (T.jx_one_le c n) (T.jx_le c n) (T.jx_one_le (c + 1) n) (T.jx_le (c + 1) n)
    (T.xphase_m4 c n 1 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 1 + 1 = 12 + 4 * D.P + 2 by omega]
        exact T.xphase_m4 c n 2 (by omega) (by omega))
    (T.xphase_m4 (c + 1) n 1 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 1 + 1 = 12 + 4 * D.P + 2 by omega]
        exact T.xphase_m4 (c + 1) n 2 (by omega) (by omega))
    (T.cphase_m4 c n 1 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 1 + 1 = 12 + 4 * D.P + 2 by omega]
        exact T.cphase_m4 c n 2 (by omega) (by omega)) rfl rfl rfl rfl

lemma phaseOK_N6 (c n : ℤ) :
    T.PhaseOK c n (12 + 4 * D.P + 2) (D.data (12 + 4 * D.P + 2 + 1))
      (D.data (12 + 4 * D.P + 2 + 1 + 1)) := by
  have hc1 : D.data (12 + 4 * D.P + 2 + 1) = D.matchData D.g₄ 2 := by
    rw [show 12 + 4 * D.P + 2 + 1 = 13 + 4 * D.P + 2 by omega]
    exact D.data_m4 2 (by omega) (by omega)
  have hc2 : D.data (12 + 4 * D.P + 2 + 1 + 1) = D.matchData D.g₄ 3 := by
    rw [show 12 + 4 * D.P + 2 + 1 + 1 = 13 + 4 * D.P + 3 by omega]
    exact D.data_m4 3 (by omega) (by omega)
  rw [hc1, hc2]
  refine T.match_phase2 (g := D.g₄) (ℓ' := T.jx (c + 1) n) (by omega) D.g₄_bounds
    (T.jx_one_le c n) (T.jx_le c n) (T.xphase_m4 c n 2 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 2 + 1 = 12 + 4 * D.P + 3 by omega]
        exact T.xphase_m4 c n 3 (by omega) (by omega))
    (T.cphase_m4 c n 2 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 2 + 1 = 12 + 4 * D.P + 3 by omega]
        exact T.cphase_m4 c n 3 (by omega) (by omega)) rfl ?_ rfl rfl
  exact D.Aset_of_match' D.h₄_lt D.g₄_eq (T.jx_one_le c n) (T.jx_le c n) (T.alt₄ c n)

lemma phaseOK_N7 (c n : ℤ) :
    T.PhaseOK c n (12 + 4 * D.P + 3) (D.data (12 + 4 * D.P + 3 + 1))
      (D.data (12 + 4 * D.P + 3 + 1 + 1)) := by
  have hc1 : D.data (12 + 4 * D.P + 3 + 1) = D.matchData D.g₄ 3 := by
    rw [show 12 + 4 * D.P + 3 + 1 = 13 + 4 * D.P + 3 by omega]
    exact D.data_m4 3 (by omega) (by omega)
  have hc2 : D.data (12 + 4 * D.P + 3 + 1 + 1) = D.matchData D.g₄ 4 := by
    rw [show 12 + 4 * D.P + 3 + 1 + 1 = 13 + 4 * D.P + 4 by omega]
    exact D.data_m4 4 (by omega) (by omega)
  rw [hc1, hc2]
  exact T.match_phase3 (g := D.g₄) (by omega) D.g₄_bounds
    (T.jx_one_le c n) (T.jx_le c n) (T.jx_one_le (c + 1) n) (T.jx_le (c + 1) n)
    (T.xphase_m4 c n 3 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 3 + 1 = 12 + 4 * D.P + 4 by omega]
        exact T.xphase_m4 c n 4 (by omega) (by omega))
    (T.xphase_m4 (c + 1) n 3 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 3 + 1 = 12 + 4 * D.P + 4 by omega]
        exact T.xphase_m4 (c + 1) n 4 (by omega) (by omega))
    (T.cphase_m4 c n 3 (by omega) (by omega))
    (by rw [show 12 + 4 * D.P + 3 + 1 = 12 + 4 * D.P + 4 by omega]
        exact T.cphase_m4 c n 4 (by omega) (by omega)) rfl rfl rfl rfl

/-! ### The second free gadget -/

lemma phaseOK_N8 (c n : ℤ) :
    T.PhaseOK c n (12 + 4 * D.P + 4) (D.data (12 + 4 * D.P + 4 + 1))
      (D.data (12 + 4 * D.P + 4 + 1 + 1)) := by
  have hP := D.one_le_P
  have hL1 := T.jx_one_le c n
  have hL2 := T.jx_le c n
  have hcur : D.data (12 + 4 * D.P + 4 + 1) = D.matchData D.g₄ 4 := by
    rw [show 12 + 4 * D.P + 4 + 1 = 13 + 4 * D.P + 4 by omega]
    exact D.data_m4 4 (by omega) (by omega)
  have hnxt : D.data (12 + 4 * D.P + 4 + 1 + 1) = ⟨D.Efull, D.C₂ 1, -1, D.d - 1⟩ := by
    have h2 := D.freeData₂_odd 1 (by omega) hP
    norm_num at h2
    rw [show 12 + 4 * D.P + 4 + 1 + 1 = 17 + 4 * D.P + 1 by omega,
      D.data_f2 1 (by omega) (by omega), h2]
  have e4 := D.mxv_mem_Eset (g := D.g₄) (ℓ := T.jx c n) (i := 4) (Or.inr (Or.inr rfl)) hL1 hL2
  have hstep := D.comp2_step (c := c) (L := T.jx c n) (p := 0)
  rw [D.comp2_zero (T.jx_A c n)] at hstep
  simp only [zero_add] at hstep
  rw [hcur, hnxt]
  refine T.free_even (u := D.d * T.jx c n) (u' := D.comp2 c (T.jx c n) 1) (by omega) ?_ ?_ ?_ ?_
    ?_ ?_ hstep.1 hstep.2
  · rw [T.xphase_m4 c n 4 (by omega) (by omega), D.mxv_four]
  · have h := T.xphase_c2_odd c n 1 (by omega) hP
    rw [show 12 + 4 * D.P + 4 + 1 = 15 + 4 * D.P + 2 * 1 by omega, h]
    norm_num
  · rw [T.cphase_m4 c n 4 (by omega) (by omega)]; unfold mcorr; norm_num
  · exact T.cphase_free2 c n (12 + 4 * D.P + 4 + 1) (by omega)
  · rw [← D.mxv_four D.g₄ (T.jx c n)]; exact e4.2.1
  · rw [← D.mxv_four D.g₄ (T.jx c n)]; exact e4.2.2

lemma phaseOK_c2_odd (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ D.P) :
    T.PhaseOK c n (15 + 4 * D.P + 2 * p) (D.data (16 + 4 * D.P + 2 * p))
      (D.data (17 + 4 * D.P + 2 * p)) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound hp2
  have hcur : D.data (16 + 4 * D.P + 2 * p) = ⟨D.Efull, D.C₂ (p : ℤ), -1, D.d - 1⟩ := by
    rw [show 16 + 4 * D.P + 2 * p = 17 + 4 * D.P + (2 * p - 1) by omega,
      D.data_f2 (2 * p - 1) (by omega) (by omega), D.freeData₂_odd p hp1 hp2]
  have hnxt : D.data (17 + 4 * D.P + 2 * p) = ⟨D.C₂ (p : ℤ), D.Efull, 0, 0⟩ := by
    rw [D.data_f2 (2 * p) (by omega) (by omega), D.freeData₂_even p hp2]
  have hm := D.comp2_mem (c := c) (L := T.jx c n) (p := (p : ℤ)) (T.jx_one_le c n) (T.jx_le c n)
    (T.jx_A c n) (T.jx_B c n) hpb.1 hpb.2
  rw [hcur, hnxt]
  exact T.free_odd (by omega) (T.xphase_c2_odd c n p hp1 hp2)
    (by rw [show 15 + 4 * D.P + 2 * p + 1 = 16 + 4 * D.P + 2 * p by omega]
        exact T.xphase_c2_even c n p hp1 hp2)
    (T.xphase_c2_odd (c + 1) n p hp1 hp2)
    (by rw [show 15 + 4 * D.P + 2 * p + 1 = 16 + 4 * D.P + 2 * p by omega]
        exact T.xphase_c2_even (c + 1) n p hp1 hp2)
    (T.cphase_free2 c n (15 + 4 * D.P + 2 * p) (by omega))
    (T.cphase_free2 c n (15 + 4 * D.P + 2 * p + 1) (by omega)) hm.1 hm.2.2 rfl rfl

lemma phaseOK_c2_even (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p < D.P) :
    T.PhaseOK c n (16 + 4 * D.P + 2 * p) (D.data (17 + 4 * D.P + 2 * p))
      (D.data (18 + 4 * D.P + 2 * p)) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound (le_of_lt hp2)
  have hcur : D.data (17 + 4 * D.P + 2 * p) = ⟨D.C₂ (p : ℤ), D.Efull, 0, 0⟩ := by
    rw [D.data_f2 (2 * p) (by omega) (by omega), D.freeData₂_even p (by omega)]
  have hnxt : D.data (18 + 4 * D.P + 2 * p) = ⟨D.Efull, D.C₂ ((p : ℤ) + 1), -1, D.d - 1⟩ := by
    have h2 := D.freeData₂_odd (p + 1) (by omega) (by omega)
    rw [show 18 + 4 * D.P + 2 * p = 17 + 4 * D.P + (2 * (p + 1) - 1) by omega,
      D.data_f2 (2 * (p + 1) - 1) (by omega) (by omega), h2]
    norm_num
  have hm := D.comp2_mem (c := c) (L := T.jx c n) (p := (p : ℤ)) (T.jx_one_le c n) (T.jx_le c n)
    (T.jx_A c n) (T.jx_B c n) hpb.1 hpb.2
  have hstep := D.comp2_step (c := c) (L := T.jx c n) (p := (p : ℤ))
  rw [hcur, hnxt]
  refine T.free_even (u := D.comp2 c (T.jx c n) (p : ℤ))
    (u' := D.comp2 c (T.jx c n) ((p : ℤ) + 1)) (by omega)
    (T.xphase_c2_even c n p hp1 (by omega)) ?_
    (T.cphase_free2 c n (16 + 4 * D.P + 2 * p) (by omega))
    (T.cphase_free2 c n (16 + 4 * D.P + 2 * p + 1) (by omega)) hm.1 hm.2.2 hstep.1 hstep.2
  have h := T.xphase_c2_odd c n (p + 1) (by omega) (by omega)
  rw [show 16 + 4 * D.P + 2 * p + 1 = 15 + 4 * D.P + 2 * (p + 1) by omega, h]
  norm_num

lemma phaseOK_c2_mid (c n : ℤ) :
    T.PhaseOK c n (16 + 4 * D.P + 2 * D.P) (D.data (17 + 4 * D.P + 2 * D.P))
      (D.data (18 + 4 * D.P + 2 * D.P)) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound (le_refl D.P)
  have hcur : D.data (17 + 4 * D.P + 2 * D.P) = ⟨D.C₂ (D.P : ℤ), D.Efull, 0, 0⟩ := by
    rw [D.data_f2 (2 * D.P) (by omega) (by omega), D.freeData₂_even D.P (by omega)]
  have hnxt : D.data (18 + 4 * D.P + 2 * D.P) = ⟨D.Efull, D.D₂ 1, -D.d + 1, 1⟩ := by
    have h2 := D.freeData₂_exp_odd 1 (by omega)
    norm_num at h2
    rw [show 18 + 4 * D.P + 2 * D.P = 17 + 4 * D.P + (2 * D.P + 1) by omega,
      D.data_f2 (2 * D.P + 1) (by omega) (by omega), h2]
  have hm := D.comp2_mem (c := c) (L := T.jx c n) (p := (D.P : ℤ)) (T.jx_one_le c n)
    (T.jx_le c n) (T.jx_A c n) (T.jx_B c n) hpb.1 hpb.2
  have hstep := D.comp2_exp2_step (c := c) (L := T.jx c n) (M := T.ix c (n + 1)) (T.jx_A c n)
    (T.ix_A c (n + 1)) (fun h => (T.lockB' c n h).symm) (T.jx_one_le c n)
  rw [hcur, hnxt]
  rw [D.pz_cast] at hm
  refine T.free_even (u := D.comp2 c (T.jx c n) D.pz) (u' := D.exp2 c (T.ix c (n + 1)) 1)
    (by omega) ?_ ?_ (T.cphase_free2 c n (16 + 4 * D.P + 2 * D.P) (by omega))
    (T.cphase_free2 c n (16 + 4 * D.P + 2 * D.P + 1) (by omega)) hm.1 hm.2.2 hstep.1 hstep.2
  · rw [← D.pz_cast]; exact T.xphase_c2_even c n D.P (by omega) (by omega)
  · have h := T.xphase_e2_odd c n 1 (by omega) hP
    rw [show 16 + 4 * D.P + 2 * D.P + 1 = 15 + 6 * D.P + 2 * 1 by omega, h]
    norm_num

lemma phaseOK_e2_odd (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p < D.P) :
    T.PhaseOK c n (15 + 6 * D.P + 2 * p) (D.data (16 + 6 * D.P + 2 * p))
      (D.data (17 + 6 * D.P + 2 * p)) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound (le_of_lt hp2)
  have hcur : D.data (16 + 6 * D.P + 2 * p) = ⟨D.Efull, D.D₂ (p : ℤ), -D.d + 1, 1⟩ := by
    rw [show 16 + 6 * D.P + 2 * p = 17 + 4 * D.P + (2 * D.P + 2 * p - 1) by omega,
      D.data_f2 (2 * D.P + 2 * p - 1) (by omega) (by omega),
      D.freeData₂_exp_odd p hp1]
  have hnxt : D.data (17 + 6 * D.P + 2 * p) = ⟨D.D₂ (p : ℤ), D.Efull, 0, 0⟩ := by
    rw [show 17 + 6 * D.P + 2 * p = 17 + 4 * D.P + (2 * D.P + 2 * p) by omega,
      D.data_f2 (2 * D.P + 2 * p) (by omega) (by omega),
      D.freeData₂_exp_even p hp1]
  have hm := D.exp2_mem (c := c) (M := T.ix c (n + 1)) (p := (p : ℤ)) (T.ix_one_le c (n + 1))
    (T.ix_le c (n + 1)) (T.ix_A c (n + 1)) (T.ix_B c (n + 1)) hpb.1 hpb.2
  rw [hcur, hnxt]
  exact T.free_odd (by omega) (T.xphase_e2_odd c n p hp1 (by omega))
    (by rw [show 15 + 6 * D.P + 2 * p + 1 = 16 + 6 * D.P + 2 * p by omega]
        exact T.xphase_e2_even c n p hp1 (by omega))
    (T.xphase_e2_odd (c + 1) n p hp1 (by omega))
    (by rw [show 15 + 6 * D.P + 2 * p + 1 = 16 + 6 * D.P + 2 * p by omega]
        exact T.xphase_e2_even (c + 1) n p hp1 (by omega))
    (T.cphase_free2 c n (15 + 6 * D.P + 2 * p) (by omega))
    (T.cphase_free2 c n (15 + 6 * D.P + 2 * p + 1) (by omega)) hm.1 hm.2.2 rfl rfl

lemma phaseOK_e2_even (c n : ℤ) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p < D.P) :
    T.PhaseOK c n (16 + 6 * D.P + 2 * p) (D.data (17 + 6 * D.P + 2 * p))
      (D.data (18 + 6 * D.P + 2 * p)) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound (le_of_lt hp2)
  have hcur : D.data (17 + 6 * D.P + 2 * p) = ⟨D.D₂ (p : ℤ), D.Efull, 0, 0⟩ := by
    rw [show 17 + 6 * D.P + 2 * p = 17 + 4 * D.P + (2 * D.P + 2 * p) by omega,
      D.data_f2 (2 * D.P + 2 * p) (by omega) (by omega),
      D.freeData₂_exp_even p hp1]
  have hnxt : D.data (18 + 6 * D.P + 2 * p) = ⟨D.Efull, D.D₂ ((p : ℤ) + 1), -D.d + 1, 1⟩ := by
    have h2 := D.freeData₂_exp_odd (p + 1) (by omega)
    rw [show 18 + 6 * D.P + 2 * p = 17 + 4 * D.P + (2 * D.P + 2 * (p + 1) - 1) by omega,
      D.data_f2 (2 * D.P + 2 * (p + 1) - 1) (by omega) (by omega), h2]
    norm_num
  have hm := D.exp2_mem (c := c) (M := T.ix c (n + 1)) (p := (p : ℤ)) (T.ix_one_le c (n + 1))
    (T.ix_le c (n + 1)) (T.ix_A c (n + 1)) (T.ix_B c (n + 1)) hpb.1 hpb.2
  have hstep := D.exp2_step (c := c) (M := T.ix c (n + 1)) (p := (p : ℤ))
  rw [hcur, hnxt]
  refine T.free_even (u := D.exp2 c (T.ix c (n + 1)) (p : ℤ))
    (u' := D.exp2 c (T.ix c (n + 1)) ((p : ℤ) + 1)) (by omega)
    (T.xphase_e2_even c n p hp1 (by omega)) ?_
    (T.cphase_free2 c n (16 + 6 * D.P + 2 * p) (by omega))
    (T.cphase_free2 c n (16 + 6 * D.P + 2 * p + 1) (by omega)) hm.1 hm.2.2 hstep.1 hstep.2
  have h := T.xphase_e2_odd c n (p + 1) (by omega) (by omega)
  rw [show 16 + 6 * D.P + 2 * p + 1 = 15 + 6 * D.P + 2 * (p + 1) by omega, h]
  norm_num

lemma phaseOK_last (c n : ℤ) :
    T.PhaseOK c n (15 + 6 * D.P + 2 * D.P) (D.data (16 + 6 * D.P + 2 * D.P)) (D.data 1) := by
  have hP := D.one_le_P
  have hpb := D.pz_bound (le_refl D.P)
  have hcur : D.data (16 + 6 * D.P + 2 * D.P) = ⟨D.Efull, D.D₂ (D.P : ℤ), -D.d + 1, 1⟩ := by
    rw [show 16 + 6 * D.P + 2 * D.P = 17 + 4 * D.P + (2 * D.P + 2 * D.P - 1) by omega,
      D.data_f2 (2 * D.P + 2 * D.P - 1) (by omega) (by omega),
      D.freeData₂_exp_odd D.P (by omega)]
  have hm := D.exp2_mem (c := c) (M := T.ix c (n + 1)) (p := (D.P : ℤ)) (T.ix_one_le c (n + 1))
    (T.ix_le c (n + 1)) (T.ix_A c (n + 1)) (T.ix_B c (n + 1)) hpb.1 hpb.2
  rw [hcur]
  exact T.free_odd (by omega) (T.xphase_e2_odd c n D.P (by omega) (by omega))
    (by rw [show 15 + 6 * D.P + 2 * D.P + 1 = 16 + 6 * D.P + 2 * D.P by omega]
        exact T.xphase_e2_even c n D.P (by omega) (by omega))
    (T.xphase_e2_odd (c + 1) n D.P (by omega) (by omega))
    (by rw [show 15 + 6 * D.P + 2 * D.P + 1 = 16 + 6 * D.P + 2 * D.P by omega]
        exact T.xphase_e2_even (c + 1) n D.P (by omega) (by omega))
    (T.cphase_free2 c n (15 + 6 * D.P + 2 * D.P) (by omega))
    (T.cphase_free2 c n (15 + 6 * D.P + 2 * D.P + 1) (by omega)) hm.1 hm.2.2 rfl rfl

/-! ### Every phase satisfies the gap conditions -/

theorem phaseOK_main (c n : ℤ) (j : ℕ) (hj : j + 1 < D.sN) :
    T.PhaseOK c n j (D.data (j + 1)) (D.data (j + 2)) := by
  have hP := D.one_le_P
  have hsN : D.sN = 16 + 8 * D.P := rfl
  by_cases h8 : j ≤ 8
  · interval_cases j
    · exact T.phaseOK_0 c n
    · exact T.phaseOK_1 c n
    · exact T.phaseOK_2 c n
    · exact T.phaseOK_3 c n
    · exact T.phaseOK_4 c n
    · exact T.phaseOK_5 c n
    · exact T.phaseOK_6 c n
    · exact T.phaseOK_7 c n
    · exact T.phaseOK_8 c n
  by_cases h2 : j ≤ 8 + 2 * D.P
  · by_cases hpar : j % 2 = 0
    · obtain ⟨p, rfl⟩ : ∃ p, j = 8 + 2 * p := ⟨(j - 8) / 2, by omega⟩
      by_cases hlast : p = D.P
      · subst hlast
        rw [show 8 + 2 * D.P + 1 = 9 + 2 * D.P by omega,
          show 8 + 2 * D.P + 2 = 10 + 2 * D.P by omega]
        exact T.phaseOK_c1_mid c n
      · rw [show 8 + 2 * p + 1 = 9 + 2 * p by omega, show 8 + 2 * p + 2 = 10 + 2 * p by omega]
        exact T.phaseOK_c1_even c n p (by omega) (by omega)
    · obtain ⟨p, rfl⟩ : ∃ p, j = 7 + 2 * p := ⟨(j - 7) / 2, by omega⟩
      rw [show 7 + 2 * p + 1 = 8 + 2 * p by omega, show 7 + 2 * p + 2 = 9 + 2 * p by omega]
      exact T.phaseOK_c1_odd c n p (by omega) (by omega)
  by_cases h4 : j ≤ 8 + 4 * D.P
  · by_cases hpar : j % 2 = 0
    · obtain ⟨p, rfl⟩ : ∃ p, j = 8 + 2 * D.P + 2 * p := ⟨(j - 8 - 2 * D.P) / 2, by omega⟩
      by_cases hlast : p = D.P
      · subst hlast
        rw [show 8 + 2 * D.P + 2 * D.P = 8 + 4 * D.P by omega]
        exact T.phaseOK_N c n
      · rw [show 8 + 2 * D.P + 2 * p + 1 = 9 + 2 * D.P + 2 * p by omega,
          show 8 + 2 * D.P + 2 * p + 2 = 10 + 2 * D.P + 2 * p by omega]
        exact T.phaseOK_e1_even c n p (by omega) (by omega)
    · obtain ⟨p, rfl⟩ : ∃ p, j = 7 + 2 * D.P + 2 * p := ⟨(j - 7 - 2 * D.P) / 2, by omega⟩
      rw [show 7 + 2 * D.P + 2 * p + 1 = 8 + 2 * D.P + 2 * p by omega,
        show 7 + 2 * D.P + 2 * p + 2 = 9 + 2 * D.P + 2 * p by omega]
      exact T.phaseOK_e1_odd c n p (by omega) (by omega)
  by_cases h5 : j ≤ 16 + 4 * D.P
  · obtain ⟨i, rfl⟩ : ∃ i, j = 8 + 4 * D.P + i := ⟨j - 8 - 4 * D.P, by omega⟩
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ 8 := by omega
    interval_cases i
    · exact T.phaseOK_N1 c n
    · exact T.phaseOK_N2 c n
    · exact T.phaseOK_N3 c n
    · exact T.phaseOK_N4 c n
    · rw [show 8 + 4 * D.P + 5 = 12 + 4 * D.P + 1 by omega]
      exact T.phaseOK_N5 c n
    · rw [show 8 + 4 * D.P + 6 = 12 + 4 * D.P + 2 by omega]
      exact T.phaseOK_N6 c n
    · rw [show 8 + 4 * D.P + 7 = 12 + 4 * D.P + 3 by omega]
      exact T.phaseOK_N7 c n
    · rw [show 8 + 4 * D.P + 8 = 12 + 4 * D.P + 4 by omega]
      exact T.phaseOK_N8 c n
  by_cases h6 : j ≤ 16 + 6 * D.P
  · by_cases hpar : j % 2 = 0
    · obtain ⟨p, rfl⟩ : ∃ p, j = 16 + 4 * D.P + 2 * p := ⟨(j - 16 - 4 * D.P) / 2, by omega⟩
      by_cases hlast : p = D.P
      · subst hlast
        rw [show 16 + 4 * D.P + 2 * D.P + 1 = 17 + 4 * D.P + 2 * D.P by omega,
          show 16 + 4 * D.P + 2 * D.P + 2 = 18 + 4 * D.P + 2 * D.P by omega]
        exact T.phaseOK_c2_mid c n
      · rw [show 16 + 4 * D.P + 2 * p + 1 = 17 + 4 * D.P + 2 * p by omega,
          show 16 + 4 * D.P + 2 * p + 2 = 18 + 4 * D.P + 2 * p by omega]
        exact T.phaseOK_c2_even c n p (by omega) (by omega)
    · obtain ⟨p, rfl⟩ : ∃ p, j = 15 + 4 * D.P + 2 * p := ⟨(j - 15 - 4 * D.P) / 2, by omega⟩
      rw [show 15 + 4 * D.P + 2 * p + 1 = 16 + 4 * D.P + 2 * p by omega,
        show 15 + 4 * D.P + 2 * p + 2 = 17 + 4 * D.P + 2 * p by omega]
      exact T.phaseOK_c2_odd c n p (by omega) (by omega)
  · by_cases hpar : j % 2 = 0
    · obtain ⟨p, rfl⟩ : ∃ p, j = 16 + 6 * D.P + 2 * p := ⟨(j - 16 - 6 * D.P) / 2, by omega⟩
      rw [show 16 + 6 * D.P + 2 * p + 1 = 17 + 6 * D.P + 2 * p by omega,
        show 16 + 6 * D.P + 2 * p + 2 = 18 + 6 * D.P + 2 * p by omega]
      exact T.phaseOK_e2_even c n p (by omega) (by omega)
    · obtain ⟨p, rfl⟩ : ∃ p, j = 15 + 6 * D.P + 2 * p := ⟨(j - 15 - 6 * D.P) / 2, by omega⟩
      rw [show 15 + 6 * D.P + 2 * p + 1 = 16 + 6 * D.P + 2 * p by omega,
        show 15 + 6 * D.P + 2 * p + 2 = 17 + 6 * D.P + 2 * p by omega]
      exact T.phaseOK_e2_odd c n p (by omega) (by omega)

/-- The gap conditions at the time `m`, together with the identification of the values at the
time `m + 1` with the values at the next phase (which wrap around at the end of a cycle). -/
theorem step_facts (c m : ℤ) :
    T.PhaseOK c (D.cyc m) (D.pha m) (D.data (D.pha m + 1)) (D.data (D.pha (m + 1) + 1)) ∧
      T.xphase c (D.cyc (m + 1)) (D.pha (m + 1)) = T.xphase c (D.cyc m) (D.pha m + 1) ∧
      T.yphase c (D.cyc (m + 1)) (D.pha (m + 1)) = T.yphase c (D.cyc m) (D.pha m + 1) ∧
      T.xphase (c + 1) (D.cyc (m + 1)) (D.pha (m + 1)) =
        T.xphase (c + 1) (D.cyc m) (D.pha m + 1) := by
  have hP := D.one_le_P
  have hsN : D.sN = 16 + 8 * D.P := rfl
  have hlt := D.pha_lt m
  by_cases hlast : D.pha m + 1 = D.sN
  · obtain ⟨h0, hc⟩ := D.pha_succ_eq hlast
    have hj : D.pha m = 15 + 6 * D.P + 2 * D.P := by omega
    have hj1 : D.pha m + 1 = D.sN := hlast
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h0, hj]
      have := T.phaseOK_last c (D.cyc m)
      rw [show 16 + 6 * D.P + 2 * D.P = 15 + 6 * D.P + 2 * D.P + 1 by omega] at this
      exact this
    · rw [h0, hc, hj1, T.xphase_wrap]
    · rw [h0, hc, hj1, T.yphase_wrap]
    · rw [h0, hc, hj1, T.xphase_wrap]
  · obtain ⟨h0, hc⟩ := D.pha_succ_lt (m := m) (by omega)
    refine ⟨?_, by rw [h0, hc], by rw [h0, hc], by rw [h0, hc]⟩
    rw [h0]
    exact T.phaseOK_main c (D.cyc m) (D.pha m) (by omega)

/-! ### The line assignment -/

/-- The line assignment built from an index tiling. -/
def lineOfIndex : LineAssignment D.spec where
  st := fun r => D.pha (-r) + 1
  V := fun J r =>
    if J % 2 = 0 then T.xphase (J / 2) (D.cyc (-r)) (D.pha (-r))
    else T.yphase ((J - 1) / 2) (D.cyc (-r)) (D.pha (-r))
  state_mem := by
    intro r
    have := D.pha_lt (-r)
    exact ⟨by omega, by simp only [ABData.spec_s]; omega⟩
  state_cycle := by
    intro r
    have hm : -(r - 1) = -r + 1 := by ring
    show D.pha (-(r - 1)) + 1 = GapSpec.sigma _ _
    unfold GapSpec.sigma
    simp only [ABData.spec_s]
    rw [hm]
    by_cases hlast : D.pha (-r) + 1 = D.sN
    · rw [(D.pha_succ_eq hlast).1, if_pos hlast]
    · rw [(D.pha_succ_lt (by have := D.pha_lt (-r); omega)).1, if_neg hlast]
  memL := by
    intro r J hJ
    have hpar : (-r) % 2 = 0 ∨ (-r) % 2 = 1 := by omega
    by_cases hJe : J % 2 = 0
    · have hme : D.pha (-r) % 2 = 0 := by
        rw [← D.even_iff_pha_even]
        refine ⟨(-r) / 2, by omega⟩
      simp only [hJe, if_pos, ABData.spec_L]
      obtain ⟨hev, -⟩ := T.step_facts (J / 2) (-r)
      exact (hev.1 hme).1
    · have hmo : D.pha (-r) % 2 = 1 := by
        have : ¬ Even (-r) := by
          intro he
          obtain ⟨k, hk⟩ := he
          omega
        have := (D.even_iff_pha_even (-r)).not.2
        have hlt := D.pha_lt (-r)
        by_contra hcon
        exact ‹¬ Even (-r)› ((D.even_iff_pha_even (-r)).2 (by omega))
      simp only [if_neg hJe, ABData.spec_L]
      obtain ⟨hev, -⟩ := T.step_facts ((J - 1) / 2) (-r)
      exact (hev.2 hmo).2.1
  memR := by
    intro r J hJ
    by_cases hJe : J % 2 = 0
    · have hmo : D.pha (-r) % 2 = 1 := by
        have hne : ¬ Even (-r) := by
          intro he
          obtain ⟨k, hk⟩ := he
          omega
        have hlt := D.pha_lt (-r)
        by_contra hcon
        exact hne ((D.even_iff_pha_even (-r)).2 (by omega))
      simp only [hJe, if_pos, ABData.spec_R]
      obtain ⟨hev, -⟩ := T.step_facts (J / 2) (-r)
      exact (hev.2 hmo).1
    · have hme : D.pha (-r) % 2 = 0 := by
        rw [← D.even_iff_pha_even]
        exact ⟨(-r + 1) / 2, by omega⟩
      simp only [if_neg hJe, ABData.spec_R]
      obtain ⟨hev, -⟩ := T.step_facts ((J - 1) / 2) (-r)
      exact (hev.1 hme).2.1
  pair := by
    intro r J hJ
    have hm : -(r - 1) = -r + 1 := by ring
    by_cases hJe : J % 2 = 0
    · have hme : D.pha (-r) % 2 = 0 := by
        rw [← D.even_iff_pha_even]
        exact ⟨(-r) / 2, by omega⟩
      obtain ⟨hev, hx, hy, -⟩ := T.step_facts (J / 2) (-r)
      have hJ1 : ¬ (J + 1) % 2 = 0 := by omega
      simp only [hJe, if_pos, if_neg hJ1, hm]
      rw [show (J + 1 - 1) / 2 = J / 2 by omega, hx, hy]
      have := (hev.1 hme).2.2.1
      omega
    · have hmo : D.pha (-r) % 2 = 1 := by
        have hne : ¬ Even (-r) := by
          intro he
          obtain ⟨k, hk⟩ := he
          omega
        have hlt := D.pha_lt (-r)
        by_contra hcon
        exact hne ((D.even_iff_pha_even (-r)).2 (by omega))
      obtain ⟨hev, -, hy, hx1⟩ := T.step_facts ((J - 1) / 2) (-r)
      have hJ1 : (J + 1) % 2 = 0 := by omega
      simp only [if_neg hJe, hJ1, if_pos, hm]
      rw [show (J + 1) / 2 = (J - 1) / 2 + 1 by omega, hy, hx1]
      have := (hev.2 hmo).2.2.1
      omega
  intv := by
    intro r J hJ
    have hm : -(r - 1) = -r + 1 := by ring
    have hstate : D.spec.Imin (D.pha (-(r - 1)) + 1) = (D.data (D.pha (-r + 1) + 1)).lo ∧
        D.spec.Imax (D.pha (-(r - 1)) + 1) = (D.data (D.pha (-r + 1) + 1)).hi := by
      rw [hm]; exact ⟨rfl, rfl⟩
    rw [hstate.1, hstate.2]
    by_cases hJe : J % 2 = 0
    · have hme : D.pha (-r) % 2 = 0 := by
        rw [← D.even_iff_pha_even]
        exact ⟨(-r) / 2, by omega⟩
      obtain ⟨hev, hx, -⟩ := T.step_facts (J / 2) (-r)
      simp only [hJe, if_pos, hm]
      rw [hx]
      exact (hev.1 hme).2.2.2
    · have hmo : D.pha (-r) % 2 = 1 := by
        have hne : ¬ Even (-r) := by
          intro he
          obtain ⟨k, hk⟩ := he
          omega
        have hlt := D.pha_lt (-r)
        by_contra hcon
        exact hne ((D.even_iff_pha_even (-r)).2 (by omega))
      obtain ⟨hev, -, hy, -⟩ := T.step_facts ((J - 1) / 2) (-r)
      simp only [if_neg hJe, hm]
      rw [hy]
      exact (hev.2 hmo).2.2.2

end IndexTiling

/-- **The easy direction of Sections 2.6–2.8**: if the data built from a set of AB tiles admits
an index tiling, then its buckets admit a gap assignment. -/
theorem nonempty_gapAssignment_of_indexTiling {D : ABData} (T : IndexTiling D) :
    Nonempty (GapAssignment D.spec) :=
  (nonempty_gapAssignment_iff_lineAssignment D.spec).2 ⟨T.lineOfIndex⟩

end ABSim

end StickPolyhex
