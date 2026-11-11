import Tiling.Proofs.ABBackward

/-!
# The index tiling carried by a gap assignment

`Tiling/Proofs/ABBackward.lean` reads one cycle of the buckets and extracts, for every column
`c` and every band `n`, the index `Backward.idx A r₀ c n` of the value carried at the bottom of
the band and the index `Backward.jdx A r₀ c n` of the value carried in its middle.  This file
turns those two families into an `IndexTiling`:

* `Backward.alt₁`, …, `Backward.alt₄` are the four conditions forced by the four matching
  gadgets: the kinds of the indices of two adjacent columns alternate, and the colors read by
  `h₁, …, h₄` agree across the boundaries of the appropriate direction;
* `Backward.lock_mid` and `Backward.lock_next` are the two conditions forced by the two free
  gadgets: an `A` column keeps its index from the bottom of a band to its middle, and a `B`
  column keeps its index from the middle of a band to the bottom of the next one;
* consequently the kind of a column does not depend on the band (`Backward.idx_indep`) and
  alternates with the column (`Backward.idx_parity`), so that after the shift
  `Backward.shift` — which is `0` or `1` — the even columns are exactly the `A` columns.

The main result is `ABSim.nonempty_indexTiling_of_gapAssignment`.
-/

namespace StickPolyhex

namespace ABSim

namespace Backward

variable {D : ABData} {A : LineAssignment D.spec} {r₀ : ℤ}

/-! ### The values at the bottom and in the middle of a band -/

lemma idx_eq (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    Xv A r₀ c ((D.sN : ℤ) * n) = D.d * idx A r₀ c n ∧
      1 ≤ idx A r₀ c n ∧ idx A r₀ c n ≤ 2 * D.tz :=
  eset_slot ((cycle_facts hr₀ n).1 c)

lemma jdx_eq (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ)) = D.d * jdx A r₀ c n ∧
      1 ≤ jdx A r₀ c n ∧ jdx A r₀ c n ≤ 2 * D.tz :=
  eset_slot ((cycle_facts hr₀ n).2.1 c)

lemma isA_iff_le {D : ABData} {ℓ : ℤ} (h1 : 1 ≤ ℓ) : D.isA (D.d * ℓ) ↔ ℓ ≤ D.tz := by
  have hd := D.d_pos
  constructor
  · rintro ⟨ℓ', h1', h2', he⟩
    have heq : D.d * ℓ + 0 = D.d * ℓ' + 0 := by omega
    obtain ⟨hll, -⟩ := D.slot_unique heq (by omega) (by omega)
    omega
  · intro h
    exact ⟨ℓ, h1, h, rfl⟩

lemma isB_iff_lt {D : ABData} {ℓ : ℤ} (h2 : ℓ ≤ 2 * D.tz) : D.isB (D.d * ℓ) ↔ D.tz < ℓ := by
  have hd := D.d_pos
  constructor
  · rintro ⟨ℓ', h1', h2', he⟩
    have heq : D.d * ℓ + 0 = D.d * ℓ' + 0 := by omega
    obtain ⟨hll, -⟩ := D.slot_unique heq (by omega) (by omega)
    omega
  · intro h
    exact ⟨ℓ, by omega, h2, rfl⟩

/-! ### The four matching conditions -/

/-- The first matching gadget: the kinds of the indices of two adjacent columns alternate, and
the color `h₁` agrees across every boundary from an `A` column to a `B` column. -/
lemma alt₁ (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    (idx A r₀ c n ≤ D.tz ↔ ¬ idx A r₀ (c + 1) n ≤ D.tz) ∧
      (idx A r₀ c n ≤ D.tz → D.h₁ (idx A r₀ c n) = D.h₁ (idx A r₀ (c + 1) n)) :=
  D.matchA_concl (h := D.h₁) (ℓ := idx A r₀ c n) (ℓ' := idx A r₀ (c + 1) n) D.h₁_lt
    (by exact (cycle_facts hr₀ n).2.2.1 c)

/-- The second matching gadget: the color `h₂` agrees across every boundary from a `B` column to
an `A` column. -/
lemma alt₂ (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    (idx A r₀ c n ≤ D.tz ↔ ¬ idx A r₀ (c + 1) n ≤ D.tz) ∧
      (¬ idx A r₀ c n ≤ D.tz → D.h₂ (idx A r₀ c n) = D.h₂ (idx A r₀ (c + 1) n)) :=
  D.matchB_concl (h := D.h₂) (ℓ := idx A r₀ c n) (ℓ' := idx A r₀ (c + 1) n) D.h₂_lt
    (by exact (cycle_facts hr₀ n).2.2.2.1 c)

/-- The third matching gadget, read in the middle of a band. -/
lemma alt₃ (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    (jdx A r₀ c n ≤ D.tz ↔ ¬ jdx A r₀ (c + 1) n ≤ D.tz) ∧
      (jdx A r₀ c n ≤ D.tz → D.h₃ (jdx A r₀ c n) = D.h₃ (jdx A r₀ (c + 1) n)) :=
  D.matchA_concl (h := D.h₃) (ℓ := jdx A r₀ c n) (ℓ' := jdx A r₀ (c + 1) n) D.h₃_lt
    (by exact (cycle_facts hr₀ n).2.2.2.2.1 c)

/-- The fourth matching gadget, read in the middle of a band. -/
lemma alt₄ (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    (jdx A r₀ c n ≤ D.tz ↔ ¬ jdx A r₀ (c + 1) n ≤ D.tz) ∧
      (¬ jdx A r₀ c n ≤ D.tz → D.h₄ (jdx A r₀ c n) = D.h₄ (jdx A r₀ (c + 1) n)) :=
  D.matchB_concl (h := D.h₄) (ℓ := jdx A r₀ c n) (ℓ' := jdx A r₀ (c + 1) n) D.h₄_lt
    (by exact (cycle_facts hr₀ n).2.2.2.2.2.1 c)

/-! ### The two locking conditions -/

/-- An `A` column keeps its index from the bottom of a band to its middle. -/
lemma lock_mid (hr₀ : A.st r₀ = 1) (c n : ℤ) (h : idx A r₀ c n ≤ D.tz) :
    jdx A r₀ c n = idx A r₀ c n := by
  obtain ⟨hxb, h1b, h2b⟩ := idx_eq hr₀ c n
  obtain ⟨hxm, h1m, h2m⟩ := jdx_eq hr₀ c n
  have hA : D.isA (Xv A r₀ c ((D.sN : ℤ) * n)) := by
    rw [hxb]; exact (isA_iff_le h1b).2 h
  have hstep := (cycle_facts hr₀ n).2.2.2.2.2.2.1 c hA
  rw [hxm, hxb] at hstep
  exact mul_left_cancel₀ (ne_of_gt D.d_pos) hstep

/-- Only an `A` column can carry an `A` index in the middle of a band. -/
lemma lock_mid_back (hr₀ : A.st r₀ = 1) (c n : ℤ) (h : jdx A r₀ c n ≤ D.tz) :
    idx A r₀ c n ≤ D.tz := by
  obtain ⟨hxb, h1b, h2b⟩ := idx_eq hr₀ c n
  obtain ⟨hxm, h1m, h2m⟩ := jdx_eq hr₀ c n
  have hA : D.isA (Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ))) := by
    rw [hxm]; exact (isA_iff_le h1m).2 h
  have hstep := (cycle_facts hr₀ n).2.2.2.2.2.2.2.1 c hA
  rw [hxb] at hstep
  exact (isA_iff_le h1b).1 hstep

/-- A `B` column keeps its index from the middle of a band to the bottom of the next one. -/
lemma lock_next (hr₀ : A.st r₀ = 1) (c n : ℤ) (h : ¬ jdx A r₀ c n ≤ D.tz) :
    idx A r₀ c (n + 1) = jdx A r₀ c n := by
  obtain ⟨hxb, h1b, h2b⟩ := idx_eq hr₀ c (n + 1)
  obtain ⟨hxm, h1m, h2m⟩ := jdx_eq hr₀ c n
  have hB : D.isB (Xv A r₀ c ((D.sN : ℤ) * n + 8 + 4 * (D.P : ℤ))) := by
    rw [hxm]; exact (isB_iff_lt h2m).2 (by omega)
  have hstep := (cycle_facts hr₀ n).2.2.2.2.2.2.2.2.1 c hB
  rw [hxm, hxb] at hstep
  exact mul_left_cancel₀ (ne_of_gt D.d_pos) hstep

/-- Only a `B` column can carry a `B` index at the bottom of the next band. -/
lemma lock_next_back (hr₀ : A.st r₀ = 1) (c n : ℤ) (h : ¬ idx A r₀ c (n + 1) ≤ D.tz) :
    ¬ jdx A r₀ c n ≤ D.tz := by
  obtain ⟨hxb, h1b, h2b⟩ := idx_eq hr₀ c (n + 1)
  obtain ⟨hxm, h1m, h2m⟩ := jdx_eq hr₀ c n
  have hB : D.isB (Xv A r₀ c ((D.sN : ℤ) * (n + 1))) := by
    rw [hxb]; exact (isB_iff_lt h2b).2 (by omega)
  have hstep := (cycle_facts hr₀ n).2.2.2.2.2.2.2.2.2 c hB
  rw [hxm] at hstep
  have := (isB_iff_lt h2m).1 hstep
  omega

/-! ### The kind of a column does not depend on the band -/

lemma idx_shift (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    idx A r₀ c n ≤ D.tz ↔ idx A r₀ c (n + 1) ≤ D.tz := by
  constructor
  · intro h
    by_contra hcon
    exact (lock_next_back hr₀ c n hcon) (by rw [lock_mid hr₀ c n h]; exact h)
  · intro h
    by_contra hcon
    have hj : ¬ jdx A r₀ c n ≤ D.tz := fun hj => hcon (lock_mid_back hr₀ c n hj)
    rw [lock_next hr₀ c n hj] at h
    exact hj h

lemma idx_indep (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    idx A r₀ c n ≤ D.tz ↔ idx A r₀ c 0 ≤ D.tz := by
  induction n using Int.induction_on with
  | zero => exact Iff.rfl
  | succ i ih => rw [← idx_shift hr₀ c (i : ℤ)]; exact ih
  | pred i ih =>
    have h := idx_shift (A := A) (r₀ := r₀) hr₀ c (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h
    rw [h]; exact ih

/-! ### The kinds of the columns alternate -/

lemma idx_parity (hr₀ : A.st r₀ = 1) (c : ℤ) :
    (Even c → (idx A r₀ c 0 ≤ D.tz ↔ idx A r₀ 0 0 ≤ D.tz)) ∧
      (¬ Even c → (idx A r₀ c 0 ≤ D.tz ↔ ¬ idx A r₀ 0 0 ≤ D.tz)) := by
  induction c using Int.induction_on with
  | zero => exact ⟨fun _ => Iff.rfl, fun h => absurd ⟨0, by ring⟩ h⟩
  | succ i ih =>
    have halt := (alt₁ hr₀ (i : ℤ) 0).1
    have hpar : Even ((i : ℤ) + 1) ↔ ¬ Even (i : ℤ) := Int.even_add_one
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 := ih.2 (hpar.1 h)
      tauto
    · have h1 := ih.1 (by tauto)
      tauto
  | pred i ih =>
    have halt := (alt₁ hr₀ (-(i : ℤ) - 1) 0).1
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at halt
    have hpar : Even (-(i : ℤ) - 1) ↔ ¬ Even (-(i : ℤ)) := by
      rw [show -(i : ℤ) - 1 = -(i : ℤ) + (-1) by ring]
      constructor
      · rintro ⟨k, hk⟩ ⟨l, hl⟩; omega
      · intro h
        rcases Int.even_or_odd (-(i : ℤ)) with he | ⟨k, hk⟩
        · exact absurd he h
        · exact ⟨k, by omega⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 := ih.2 (hpar.1 h)
      tauto
    · have h1 := ih.1 (by tauto)
      tauto

/-! ### The shift putting the `A` columns on the even columns -/

/-- The shift of the columns which makes the even columns carry the `A` indices. -/
def shift (A : LineAssignment D.spec) (r₀ : ℤ) : ℤ := if idx A r₀ 0 0 ≤ D.tz then 0 else 1

lemma shift_even (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : Even c) (n : ℤ) :
    idx A r₀ (c + shift A r₀) n ≤ D.tz := by
  by_cases h : idx A r₀ 0 0 ≤ D.tz
  · have hsh : shift A r₀ = 0 := if_pos h
    rw [hsh, add_zero]
    exact (idx_indep hr₀ c n).2 (((idx_parity hr₀ c).1 hc).2 h)
  · have hsh : shift A r₀ = 1 := if_neg h
    have hodd : ¬ Even (c + 1) := by simpa using hc.add_one
    rw [hsh]
    exact (idx_indep hr₀ (c + 1) n).2 (((idx_parity hr₀ (c + 1)).2 hodd).2 h)

lemma shift_odd (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : ¬ Even c) (n : ℤ) :
    ¬ idx A r₀ (c + shift A r₀) n ≤ D.tz := by
  by_cases h : idx A r₀ 0 0 ≤ D.tz
  · have hsh : shift A r₀ = 0 := if_pos h
    rw [hsh, add_zero]
    intro hcon
    exact (((idx_parity hr₀ c).2 hc).1 ((idx_indep hr₀ c n).1 hcon)) h
  · have hsh : shift A r₀ = 1 := if_neg h
    have heven : Even (c + 1) := by
      rcases Int.even_or_odd c with he | ⟨k, hk⟩
      · exact absurd he hc
      · exact ⟨k + 1, by omega⟩
    rw [hsh]
    intro hcon
    exact h (((idx_parity hr₀ (c + 1)).1 heven).1 ((idx_indep hr₀ (c + 1) n).1 hcon))

/-! ### The index tiling -/

/-- The index of the column `c` at the bottom of the band `n`, after the shift. -/
def ixOf (A : LineAssignment D.spec) (r₀ : ℤ) (c n : ℤ) : ℤ := idx A r₀ (c + shift A r₀) n

/-- The index of the column `c` in the middle of the band `n`, after the shift. -/
def jxOf (A : LineAssignment D.spec) (r₀ : ℤ) (c n : ℤ) : ℤ := jdx A r₀ (c + shift A r₀) n

lemma ixOf_mem (hr₀ : A.st r₀ = 1) (c n : ℤ) :
    1 ≤ ixOf A r₀ c n ∧ ixOf A r₀ c n ≤ 2 * D.tz :=
  ⟨(idx_eq hr₀ _ n).2.1, (idx_eq hr₀ _ n).2.2⟩

lemma ixOf_even (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : Even c) (n : ℤ) : ixOf A r₀ c n ≤ D.tz :=
  shift_even hr₀ hc n

lemma ixOf_odd (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : ¬ Even c) (n : ℤ) : D.tz < ixOf A r₀ c n := by
  have := shift_odd hr₀ hc n
  unfold ixOf
  omega

lemma jxOf_even (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : Even c) (n : ℤ) :
    jxOf A r₀ c n = ixOf A r₀ c n :=
  lock_mid hr₀ _ n (shift_even hr₀ hc n)

lemma jxOf_odd (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : ¬ Even c) (n : ℤ) :
    jxOf A r₀ c n = ixOf A r₀ c (n + 1) :=
  (lock_next hr₀ _ n (fun hj => shift_odd hr₀ hc n (lock_mid_back hr₀ _ n hj))).symm

lemma jxOf_not_le (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : ¬ Even c) (n : ℤ) :
    ¬ jxOf A r₀ c n ≤ D.tz :=
  fun hj => shift_odd hr₀ hc n (lock_mid_back hr₀ _ n hj)

lemma ixOf_match₁ (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : Even c) (n : ℤ) :
    D.h₁ (ixOf A r₀ c n) = D.h₁ (ixOf A r₀ (c + 1) n) := by
  have h := (alt₁ hr₀ (c + shift A r₀) n).2 (shift_even hr₀ hc n)
  unfold ixOf
  rw [show c + 1 + shift A r₀ = c + shift A r₀ + 1 by ring]
  exact h

lemma ixOf_match₂ (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : ¬ Even c) (n : ℤ) :
    D.h₂ (ixOf A r₀ c n) = D.h₂ (ixOf A r₀ (c + 1) n) := by
  have h := (alt₂ hr₀ (c + shift A r₀) n).2 (shift_odd hr₀ hc n)
  unfold ixOf
  rw [show c + 1 + shift A r₀ = c + shift A r₀ + 1 by ring]
  exact h

lemma jxOf_match₃ (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : Even c) (n : ℤ) :
    D.h₃ (jxOf A r₀ c n) = D.h₃ (jxOf A r₀ (c + 1) n) := by
  have hle : jdx A r₀ (c + shift A r₀) n ≤ D.tz := by
    rw [lock_mid hr₀ _ n (shift_even hr₀ hc n)]
    exact shift_even hr₀ hc n
  have h := (alt₃ hr₀ (c + shift A r₀) n).2 hle
  unfold jxOf
  rw [show c + 1 + shift A r₀ = c + shift A r₀ + 1 by ring]
  exact h

lemma jxOf_match₄ (hr₀ : A.st r₀ = 1) {c : ℤ} (hc : ¬ Even c) (n : ℤ) :
    D.h₄ (jxOf A r₀ c n) = D.h₄ (jxOf A r₀ (c + 1) n) := by
  have h := (alt₄ hr₀ (c + shift A r₀) n).2 (jxOf_not_le hr₀ hc n)
  unfold jxOf
  rw [show c + 1 + shift A r₀ = c + shift A r₀ + 1 by ring]
  exact h

/-- The index tiling carried by a line assignment. -/
def indexTilingOfLine (hr₀ : A.st r₀ = 1) : IndexTiling D where
  ix := ixOf A r₀
  jx := jxOf A r₀
  ix_mem := ixOf_mem hr₀
  ix_even := fun _ n hc => ixOf_even hr₀ hc n
  ix_odd := fun _ n hc => ixOf_odd hr₀ hc n
  lockA := fun _ n hc => jxOf_even hr₀ hc n
  lockB := fun _ n hc => jxOf_odd hr₀ hc n
  match1 := fun _ n hc => ixOf_match₁ hr₀ hc n
  match2 := fun _ n hc => ixOf_match₂ hr₀ hc n
  match3 := fun _ n hc => jxOf_match₃ hr₀ hc n
  match4 := fun _ n hc => jxOf_match₄ hr₀ hc n

end Backward

/-- **The hard direction of Sections 2.6–2.8**: a gap assignment for the buckets built from a set
of AB tiles gives back an index tiling, hence a tiling by the AB tiles. -/
theorem nonempty_indexTiling_of_gapAssignment (D : ABData)
    (h : Nonempty (GapAssignment D.spec)) : Nonempty (IndexTiling D) := by
  obtain ⟨A⟩ := (nonempty_gapAssignment_iff_lineAssignment D.spec).1 h
  have hs : D.spec.s = D.sN := rfl
  have hst := A.state_mem 0
  have hr₀ : A.st (0 - ((D.sN + 1 - A.st 0 : ℕ) : ℤ)) = 1 := by
    rw [A.st_add 0 (D.sN + 1 - A.st 0), hs]
    rw [show A.st 0 - 1 + (D.sN + 1 - A.st 0) = D.sN by rw [hs] at hst; omega, Nat.mod_self]
  exact ⟨Backward.indexTilingOfLine hr₀⟩

end ABSim

end StickPolyhex
