import Tiling.Proofs.GapRows

/-!
# From the marks to the gap conditions

This file proves one direction of the main theorem: a schematic respecting the marks
`GapSpec.marking` satisfies the gap conditions of Section 2.5 of the paper.

The state of a row is the common index of the buckets above which the gaps of the row above it
lie (`Schematic.exists_state`).  The key step is `Schematic.master`, which combines the
information carried by the two triangle marks under the ends of a gap, the arrows of the bucket
above which it lies, and the pair of arrows on the bottom face of the block above it: it shows
that the state cycles and computes the lengths of the two parts of a gap in terms of the values
of the neighbouring gaps.
-/

namespace StickPolyhex

namespace GapSpec

variable (G : GapSpec)

lemma wZ_step {p q : ℕ} (h : p < q) :
    (2 * (G.v : ℤ) - 1) * ((p : ℤ) - 1) + (2 * (G.v : ℤ) - 1)
      ≤ (2 * (G.v : ℤ) - 1) * ((q : ℤ) - 1) := by
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hpq : (p : ℤ) + 1 ≤ (q : ℤ) := by exact_mod_cast h
  have h1 : (2 * (G.v : ℤ) - 1) * (((p : ℤ) - 1) + 1) ≤ (2 * (G.v : ℤ) - 1) * ((q : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith [h1, (by ring : (2 * (G.v : ℤ) - 1) * (((p : ℤ) - 1) + 1)
    = (2 * (G.v : ℤ) - 1) * ((p : ℤ) - 1) + (2 * (G.v : ℤ) - 1))]

end GapSpec

namespace Schematic

variable {G : GapSpec} {S : Schematic G.blockLen}

/-- Every gap lies below a block of the row above. -/
lemma exists_block_above {ρ u' : ℤ} {l' m' j' : ℕ} (hg' : S.GapData ρ u' l' m' j') :
    ∃ (c u₁ : ℤ) (l₁ m₁ j₁ l₂ m₂ j₂ : ℕ),
      S.slot (ρ + 1) c = .block 0 ∧ c ≤ u' ∧ u' + l' + m' - 1 ≤ c + G.blockLen ∧
      S.GapData (ρ + 1) u₁ l₁ m₁ j₁ ∧ u₁ + l₁ + m₁ = c ∧
      S.GapData (ρ + 1) (c + G.blockLen + 1) l₂ m₂ j₂ := by
  have hl := hg'.toGapAt.l_pos
  have hm := hg'.toGapAt.m_pos
  have hgapcol : (S.slot ρ u').IsGap := hg'.toGapAt.isGap le_rfl (by omega)
  obtain ⟨p, hp⟩ := S.exists_block_of_not_isGap (S.not_isGap_above_of_isGap hgapcol)
  have hpn : p ≤ G.blockLen := S.block_le hp
  have hpn' : (p : ℤ) ≤ (G.blockLen : ℤ) := by exact_mod_cast hpn
  have hc : S.slot (ρ + 1) (u' - p) = .block 0 := S.slot_block_zero hp
  have hga : S.GapAt (ρ + 1 - 1) u' l' m' := by
    rw [show ρ + 1 - 1 = ρ by ring]; exact hg'.toGapAt
  have hsub := gap_below_subset hc hga (by omega) (by omega)
  obtain ⟨u₁, l₁, m₁, hgap₁, he₁⟩ := exists_left_gap hc
  obtain ⟨j₁, hg₁⟩ := exists_gapData hgap₁
  obtain ⟨l₂, m₂, hgap₂⟩ := exists_right_gap hc
  obtain ⟨j₂, hg₂⟩ := exists_gapData hgap₂
  exact ⟨u' - p, u₁, l₁, m₁, j₁, l₂, m₂, j₂, hc, hsub.1, hsub.2, hg₁, he₁, hg₂⟩

/-- The heart of the matter: for a block `X` of the row `ρ + 1` with the gaps `G₁` on its left
and `G₂` on its right, and for the gap `G'` of the row `ρ` lying below `X`, the gaps `G₁` and
`G₂` lie above the same bucket `k₁`, the gap `G'` lies above the bucket `σ k₁`, and the lengths
of the two parts of `G'` are determined by the values read at the two ends of `X`. -/
lemma master (hM : S.RespectsMarking G.marking) {ρ c u' u₁ : ℤ}
    {l' m' j' k' : ℕ} {a' b' : ℤ} {l₁ m₁ j₁ k₁ : ℕ} {a₁ b₁ : ℤ} {l₂ m₂ j₂ k₂ : ℕ} {a₂ b₂ : ℤ}
    (hc : S.slot (ρ + 1) c = .block 0)
    (hg' : S.GapData ρ u' l' m' j') (hd' : Bucketed G l' m' j' k' a' b')
    (hin1 : c ≤ u') (hin2 : u' + l' + m' - 1 ≤ c + G.blockLen)
    (hg₁ : S.GapData (ρ + 1) u₁ l₁ m₁ j₁) (he₁ : u₁ + l₁ + m₁ = c)
    (hd₁ : Bucketed G l₁ m₁ j₁ k₁ a₁ b₁)
    (hg₂ : S.GapData (ρ + 1) (c + G.blockLen + 1) l₂ m₂ j₂)
    (hd₂ : Bucketed G l₂ m₂ j₂ k₂ a₂ b₂) :
    k₁ = k₂ ∧ k' = G.sigma k₁ ∧
      (l' : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.sigma k₁ : ℤ) - 1) + b₁ ∧
      (m' : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (G.sigma k₁ : ℤ)) + a₂ := by
  obtain ⟨l'', m'', hgap'', he''⟩ := below_gap hc hg₁ he₁ hg₂
  have hb₁ := hg₁.bound
  have hj₂ : (2 : ℤ) ≤ j₂ := by exact_mod_cast hg₂.two_le
  have hga : S.GapAt (ρ + 1 - 1) u' l' m' := by
    rw [show ρ + 1 - 1 = ρ by ring]; exact hg'.toGapAt
  have hl'' : (1 : ℤ) ≤ l'' := by exact_mod_cast hgap''.l_pos
  have hm'' : (1 : ℤ) ≤ m'' := by exact_mod_cast hgap''.m_pos
  have hu : u₁ - j₁ + G.blockLen + 1 = u' :=
    gap_below_unique hgap'' hga (by omega) (by omega) hin1 hin2
  have hlm : l'' = l' ∧ m'' = m' := GapAt.unique (hu ▸ hgap'') hga
  obtain ⟨hll, hmm⟩ := hlm
  subst hll; subst hmm
  have hrel := block_relation hM hc he₁ hd₁ hg₂ hd₂ hgap'' he''
  refine ⟨hrel.1, ?_, hrel.2.1, hrel.2.2⟩
  -- the state cycles: the bucket above which `G'` lies is `σ k₁`
  have hbnd := length_bounds hM hg' hd'
  have ha' := hd'.a_mem
  have hbb₁ := hd₁.b_mem
  have hvz : (1 : ℤ) ≤ (G.v : ℤ) := by exact_mod_cast G.hv
  have hImin := G.hImin k'
  have hImax := G.hImax k'
  have hIk := G.hI k'
  have hlval := hrel.2.1
  by_contra hne
  rcases lt_trichotomy k' (G.sigma k₁) with hlt | heq | hgt
  · have := G.wZ_step hlt
    linarith [hbnd.2, hlval, this]
  · exact hne heq
  · have := G.wZ_step hgt
    linarith [hbnd.1, hlval, this]

/-- A schematic respecting the marks satisfies the gap conditions. -/
theorem gapConditions_of_respectsMarking (hM : S.RespectsMarking G.marking) :
    S.SatisfiesGapConditions G := by
  classical
  choose st hst1 hst2 hst3 using fun r : ℤ => exists_state hM (r + 1)
  -- the gaps of the row `r` lie above the bucket `st (r - 1)`
  have hbucket : ∀ (r u : ℤ) (l m j k : ℕ) (a b : ℤ), S.GapData r u l m j →
      Bucketed G l m j k a b → k = st (r - 1) := by
    intro r u l m j k a b hg hd
    exact hst3 (r - 1) u l m j k a b (by rw [show r - 1 + 1 = r by ring]; exact hg) hd
  -- the gap `G'` of the row `ρ`, its bucket and its two values
  have key : ∀ (ρ u' : ℤ) (l' m' j' k' : ℕ) (a' b' : ℤ),
      S.GapData ρ u' l' m' j' → Bucketed G l' m' j' k' a' b' →
      k' = G.sigma (st ρ) ∧
        (l' : ℤ) - (2 * (G.v : ℤ) - 1) * ((G.sigma (st ρ) : ℤ) - 1) ∈ G.L (st ρ) ∧
        (m' : ℤ) - (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (G.sigma (st ρ) : ℤ)) ∈ G.R (st ρ) := by
    intro ρ u' l' m' j' k' a' b' hg' hd'
    obtain ⟨c, u₁, l₁, m₁, j₁, l₂, m₂, j₂, hc, hin1, hin2, hg₁, he₁, hg₂⟩ :=
      exists_block_above hg'
    obtain ⟨k₁, a₁, b₁, hd₁⟩ := decode hM hg₁
    obtain ⟨k₂, a₂, b₂, hd₂⟩ := decode hM hg₂
    have hmaster := master hM hc hg' hd' hin1 hin2 hg₁ he₁ hd₁ hg₂ hd₂
    have hk₁ : k₁ = st ρ := by
      have := hbucket (ρ + 1) u₁ l₁ m₁ j₁ k₁ a₁ b₁ hg₁ hd₁
      rwa [show ρ + 1 - 1 = ρ by ring] at this
    have hk₂ : k₂ = st ρ := by rw [← hmaster.1]; exact hk₁
    have hR : a₂ ∈ G.R k₁ := by rw [hmaster.1]; exact hd₂.ha
    refine ⟨by rw [hmaster.2.1, hk₁], ?_, ?_⟩
    · rw [← hk₁, hmaster.2.2.1]
      simpa using hd₁.hb
    · rw [← hk₁, hmaster.2.2.2]
      simpa using hR
  -- the state cycles
  have hcycle : ∀ r : ℤ, st (r - 1) = G.sigma (st r) := by
    intro r
    obtain ⟨u, l, m, j, hg⟩ := exists_gap_of_row (S := S) r
    obtain ⟨k, a, b, hd⟩ := decode hM hg
    rw [← hbucket r u l m j k a b hg hd]
    exact (key r u l m j k a b hg hd).1
  -- the gap below and to the left
  have keyY : ∀ (r u : ℤ) (l m j k : ℕ) (a b : ℤ), S.GapData r u l m j →
      Bucketed G l m j k a b → ∀ (uY : ℤ) (lY mY jY : ℕ), S.GapData (r - 1) uY lY mY jY →
        uY + lY + mY = u - j →
        (mY : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.s : ℤ) - (G.sigma (st (r - 1)) : ℤ)) + a := by
    intro r u l m j k a b hg hd uY lY mY jY hgY heY
    have hbd := hg.bound
    have hj2 := hg.two_le
    have hlY : (1 : ℤ) ≤ lY := by exact_mod_cast hgY.toGapAt.l_pos
    have hmY : (1 : ℤ) ≤ mY := by exact_mod_cast hgY.toGapAt.m_pos
    have hc : S.slot ((r - 1) + 1) (u - 1 - G.blockLen) = .block 0 := by
      rw [show r - 1 + 1 = r by ring]
      have := S.slot_block_zero hg.toGapAt.blockLeft
      rwa [show u - 1 - (G.blockLen : ℤ) = u - 1 - (G.blockLen : ℤ) by ring]
    have hga : S.GapAt ((r - 1) + 1 - 1) uY lY mY := by
      rw [show r - 1 + 1 - 1 = r - 1 by ring]; exact hgY.toGapAt
    have hsub := gap_below_subset hc hga (by omega) (by omega)
    obtain ⟨u₁, l₁, m₁, hgap₁, he₁⟩ := exists_left_gap hc
    obtain ⟨j₁, hg₁⟩ := exists_gapData hgap₁
    obtain ⟨k₁, a₁, b₁, hd₁⟩ := decode hM hg₁
    have hg₂ : S.GapData ((r - 1) + 1) ((u - 1 - G.blockLen) + G.blockLen + 1) l m j := by
      rw [show r - 1 + 1 = r by ring, show u - 1 - (G.blockLen : ℤ) + G.blockLen + 1 = u by ring]
      exact hg
    obtain ⟨kY, aY, bY, hdY⟩ := decode hM hgY
    have hmaster := master hM hc hgY hdY hsub.1 hsub.2 hg₁ he₁ hd₁ hg₂ hd
    have hk₁ : k₁ = st (r - 1) := by
      have := hbucket ((r - 1) + 1) u₁ l₁ m₁ j₁ k₁ a₁ b₁ hg₁ hd₁
      rwa [show r - 1 + 1 - 1 = r - 1 by ring] at this
    rw [← hk₁]
    exact hmaster.2.2.2
  -- the gap below and to the right
  have keyZ : ∀ (r u : ℤ) (l m j k : ℕ) (a b : ℤ), S.GapData r u l m j →
      Bucketed G l m j k a b → ∀ (lZ mZ jZ : ℕ),
        S.GapData (r - 1) (u - j + G.blockLen + 1) lZ mZ jZ →
        (lZ : ℤ) = (2 * (G.v : ℤ) - 1) * ((G.sigma (st (r - 1)) : ℤ) - 1) + b := by
    intro r u l m j k a b hg hd lZ mZ jZ hgZ
    have hbd := hg.bound
    have hj2 := hg.two_le
    have hlZ : (1 : ℤ) ≤ lZ := by exact_mod_cast hgZ.toGapAt.l_pos
    have hmZ : (1 : ℤ) ≤ mZ := by exact_mod_cast hgZ.toGapAt.m_pos
    have hbdZ := hgZ.bound
    have hjZ := hgZ.two_le
    have hc : S.slot ((r - 1) + 1) (u + l + m) = .block 0 := by
      rw [show r - 1 + 1 = r by ring]; exact hg.toGapAt.blockRight
    have hga : S.GapAt ((r - 1) + 1 - 1) (u - j + G.blockLen + 1) lZ mZ := by
      rw [show r - 1 + 1 - 1 = r - 1 by ring]; exact hgZ.toGapAt
    have hsub := gap_below_subset hc hga (by omega) (by omega)
    obtain ⟨l₂, m₂, hgap₂⟩ := exists_right_gap hc
    obtain ⟨j₂, hg₂⟩ := exists_gapData hgap₂
    obtain ⟨k₂, a₂, b₂, hd₂⟩ := decode hM hg₂
    have hg₁ : S.GapData ((r - 1) + 1) u l m j := by
      rw [show r - 1 + 1 = r by ring]; exact hg
    obtain ⟨kZ, aZ, bZ, hdZ⟩ := decode hM hgZ
    have hmaster := master hM hc hgZ hdZ hsub.1 hsub.2 hg₁ rfl hd hg₂ hd₂
    have hk : k = st (r - 1) := hbucket r u l m j k a b hg hd
    rw [← hk]
    exact hmaster.2.2.1
  refine ⟨st, ⟨fun r => ⟨hst1 r, hst2 r⟩, hcycle, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- left values
    intro r u l m j hg
    obtain ⟨k, a, b, hd⟩ := decode hM hg
    have hk : k = st (r - 1) := hbucket r u l m j k a b hg hd
    have := (key r u l m j k a b hg hd).2.1
    rw [GapSpec.lval, hcycle r]
    exact this
  · -- right values
    intro r u l m j hg
    obtain ⟨k, a, b, hd⟩ := decode hM hg
    have := (key r u l m j k a b hg hd).2.2
    rw [GapSpec.rval, hcycle r]
    exact this
  · -- alignment on the left
    intro r u l m j hg uY lY mY jY hgY heY
    obtain ⟨k, a, b, hd⟩ := decode hM hg
    have hk : k = st (r - 1) := hbucket r u l m j k a b hg hd
    have hmY := keyY r u l m j k a b hg hd uY lY mY jY hgY heY
    have hst2 : st (r - 1 - 1) = G.sigma (st (r - 1)) := hcycle (r - 1)
    have heL := hd.eL
    rw [GapSpec.rval, show r - 2 = r - 1 - 1 by ring, hst2, hmY, ← hk]
    linarith
  · -- alignment on the right
    intro r u l m j hg lZ mZ jZ hgZ
    obtain ⟨k, a, b, hd⟩ := decode hM hg
    have hk : k = st (r - 1) := hbucket r u l m j k a b hg hd
    have hlZ := keyZ r u l m j k a b hg hd lZ mZ jZ hgZ
    have hst2 : st (r - 1 - 1) = G.sigma (st (r - 1)) := hcycle (r - 1)
    have heR := hd.eR
    rw [GapSpec.lval, show r - 2 = r - 1 - 1 by ring, hst2, hlZ, ← hk]
    linarith
  · -- the interval condition
    intro r u l m j hg uY lY mY jY hgY heY
    obtain ⟨k, a, b, hd⟩ := decode hM hg
    have hk : k = st (r - 1) := hbucket r u l m j k a b hg hd
    have hmY := keyY r u l m j k a b hg hd uY lY mY jY hgY heY
    have hst2 : st (r - 1 - 1) = G.sigma (st (r - 1)) := hcycle (r - 1)
    have hbnd := length_bounds hM hg hd
    rw [GapSpec.rval, GapSpec.lval, show r - 2 = r - 1 - 1 by ring, hst2, hmY, ← hk]
    constructor <;> linarith [hbnd.1, hbnd.2]

end Schematic

end StickPolyhex
