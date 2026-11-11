import Tiling.Proofs.Markings

/-!
# The tiling of a schematic satisfies the marked rules exactly when the schematic respects them

This file proves the correspondence announced in `Tiling/Proofs/Markings.lean`:
`Schematic.toTiling_satisfiesRules_iff`.

The proof enumerates the matched pairs of edges of `S.toTiling`.  By
`StickTiling.satisfiesRules_of_three` it is enough to look at the edges in the directions `E`,
`NE` and `NW` of each cell, which is done in the private lemmas `pairE`, `pairNE` and `pairNW`;
the labels are read off with the lemmas of `Tiling/Proofs/SchematicLabels.lean` and the
impossible configurations are excluded with the lemmas of `Tiling/Proofs/SchematicPairs.lean`.
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ} (S : Schematic n) (M : Marking n)

local macro "getpq" h1:ident h2:ident : tactic => `(tactic|
  (rw [Option.some.injEq] at $h1:ident $h2:ident; subst $h1:ident; subst $h2:ident))

local macro "notForbidden" : tactic => `(tactic|
  (rintro ((h | h) | (h | h)) <;> cases h <;> first | omega | simp_all))

/-! ### Pairs of labels that no rule forbids -/

section Safe

variable {M}

private lemma nfm_y1_z1 : ¬ (markedRules n M).Forbidden .y1 .z1 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_y1_b (k : ℕ) : ¬ (markedRules n M).Forbidden .y1 (.b k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_z2_b {k : ℕ} (hk : n ≤ k) : ¬ (markedRules n M).Forbidden .z2 (.b k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all
  omega

private lemma nfm_d_z1 (i : ℕ) : ¬ (markedRules n M).Forbidden (.d i) .z1 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_d_b (i k : ℕ) : ¬ (markedRules n M).Forbidden (.d i) (.b k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_z2_d {i : ℕ} (hi : n ≤ i) : ¬ (markedRules n M).Forbidden .z2 (.d i) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all
  omega

private lemma nfm_d_z2 {i : ℕ} (hi : n ≤ i) : ¬ (markedRules n M).Forbidden (.d i) .z2 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all
  omega

private lemma nfm_d_d (i k : ℕ) : ¬ (markedRules n M).Forbidden (.d i) (.d k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_z1_d (i : ℕ) : ¬ (markedRules n M).Forbidden .z1 (.d i) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_b_z2 {k : ℕ} (hk : n ≤ k) : ¬ (markedRules n M).Forbidden (.b k) .z2 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all
  omega

private lemma nfm_b_d (k i : ℕ) : ¬ (markedRules n M).Forbidden (.b k) (.d i) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_z1_y2 : ¬ (markedRules n M).Forbidden .z1 .y2 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_b_y2 (k : ℕ) : ¬ (markedRules n M).Forbidden (.b k) .y2 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_z1_a (k : ℕ) : ¬ (markedRules n M).Forbidden .z1 (.a k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_c_a (i k : ℕ) : ¬ (markedRules n M).Forbidden (.c i) (.a k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_c_c (i k : ℕ) : ¬ (markedRules n M).Forbidden (.c i) (.c k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_a_c (i k : ℕ) : ¬ (markedRules n M).Forbidden (.a i) (.c k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_a_z2 (k : ℕ) : ¬ (markedRules n M).Forbidden (.a k) .z2 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_a_x1 {k : ℕ} (hk : k ≤ 1) : ¬ (markedRules n M).Forbidden (.a k) .x1 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all
  omega

private lemma nfm_x2_c (k : ℕ) : ¬ (markedRules n M).Forbidden .x2 (.c k) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_b_x2 (k : ℕ) : ¬ (markedRules n M).Forbidden (.b k) .x2 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_b_x1 (k : ℕ) : ¬ (markedRules n M).Forbidden (.b k) .x1 := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_x1_d (i : ℕ) : ¬ (markedRules n M).Forbidden .x1 (.d i) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

private lemma nfm_x2_d (i : ℕ) : ¬ (markedRules n M).Forbidden .x2 (.d i) := by
  rintro ((h | h) | (h | h)) <;> cases h <;> simp_all

/-! ### Pairs of labels controlled by a marking -/

/-- The pair matched above the `j`-th column of a block by the bottom end of a column of the
left part of a gap; it is forbidden exactly by a left-facing arrow mark on the top at the
position `j - 1`. -/
private lemma nfm_a_y2_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 ≤ n) (hmk : j - 1 ∉ M.topArrowL) :
    ¬ (markedRules n M).Forbidden (.a (n + 1 - j)) .y2 := by
  rintro ((h | h) | (h | h))
  · cases h <;> simp_all
  · cases h <;> simp_all
    omega
  · cases h
    case topArrowL i hi hm hp hq =>
      rw [StickEdge.a.injEq] at hp
      exact hmk (by rw [show j - 1 = i by omega]; exact hm)
    all_goals simp_all
  · cases h <;> simp_all

/-- The pair matched above the `j`-th column of a block by the bottom end of a column of the
right part of a gap; it is forbidden exactly by a right-facing arrow mark on the top at the
position `j - 2`. -/
private lemma nfm_a_y1_of {j : ℕ} (h1 : 2 ≤ j) (h2 : j + 1 ≤ n) (hmk : j - 2 ∉ M.topArrowR) :
    ¬ (markedRules n M).Forbidden (.a (n + 1 - j)) .y1 := by
  rintro ((h | h) | (h | h))
  · cases h <;> simp_all
  · cases h <;> simp_all
    omega
  · cases h
    case topArrowR i hi hm hp hq =>
      rw [StickEdge.a.injEq] at hp
      exact hmk (by rw [show j - 2 = i by omega]; exact hm)
    all_goals simp_all
  · cases h <;> simp_all

/-- The pair matched below the `(m-1)`-st column of a block by the top end of a column of the
left part of a gap; it is forbidden exactly by a left-facing arrow mark on the bottom at the
position `m - 1`. -/
private lemma nfm_y1_c_of {m : ℕ} (h1 : 1 ≤ m) (hmk : m ∉ M.botArrowL) :
    ¬ (markedRules n M).Forbidden .y1 (.c (m + 1)) := by
  rintro ((h | h) | (h | h))
  · cases h <;> simp_all
  · cases h <;> simp_all
  · cases h <;> simp_all
  · cases h
    case botArrowL i hi hm hp hq =>
      rw [StickEdge.c.injEq] at hp
      exact hmk (by rw [show m = i by omega]; exact hm)
    all_goals simp_all

/-- The pair matched below the `(m-1)`-st column of a block by the top end of a column of the
right part of a gap; it is forbidden exactly by a right-facing arrow mark on the bottom at the
position `m - 2`. -/
private lemma nfm_y2_c_of {m : ℕ} (h1 : 1 ≤ m) (hmk : m - 1 ∉ M.botArrowR) :
    ¬ (markedRules n M).Forbidden .y2 (.c (m + 1)) := by
  rintro ((h | h) | (h | h))
  · cases h <;> simp_all
  · cases h <;> simp_all
  · cases h <;> simp_all
  · cases h
    case botArrowR i hi hm hp hq =>
      rw [StickEdge.c.injEq] at hp
      exact hmk (by rw [show m - 1 = i by omega]; exact hm)
    all_goals simp_all

/-- The pair matched above the `j`-th column of a block by the right end of a block of the row
above; it is forbidden unless a right-facing triangle faces the position `j - 1`. -/
private lemma nfm_a_x1_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 2 ≤ n) (hmk : j - 1 ∈ M.triangleR) :
    ¬ (markedRules n M).Forbidden (.a (n + 1 - j)) .x1 := by
  rintro ((h | h) | (h | h))
  · cases h <;> simp_all
  · cases h <;> simp_all
  · cases h
    case triangleR i hi hm hp hq =>
      rw [StickEdge.a.injEq] at hp
      exact hm (by rw [show i = j - 1 by omega]; exact hmk)
    all_goals simp_all
  · cases h <;> simp_all

/-- The pair matched above the `j`-th column of a block by the left end of a block of the row
above; it is forbidden unless a left-facing triangle faces the position `j - 1`. -/
private lemma nfm_b_z2_of {k : ℕ} (h2 : k + 1 ≤ n)
    (hmk : n - 1 - k ∈ M.triangleL) : ¬ (markedRules n M).Forbidden (.b k) .z2 := by
  rintro ((h | h) | (h | h))
  · cases h <;> simp_all
  · cases h <;> simp_all
  · cases h
    case triangleL i hi hm hp hq =>
      rw [StickEdge.b.injEq] at hp
      exact hm (by rw [show i = n - 1 - k by omega]; exact hmk)
    all_goals simp_all
  · cases h <;> simp_all

end Safe

/-! ### The edges in the direction `E` -/

/-- No matched pair of edges in the direction `E` is forbidden. -/
private lemma pairE {r x : ℤ} {s : ℕ} (hsn : s ≤ n) {p q : StickEdge}
    (hp : S.toTiling.label (cellAt n r x s) HexDir.E = some p)
    (hq : S.toTiling.label (cellAt n r (x + 1) s) HexDir.W = some q) :
    ¬ (markedRules n M).Forbidden p q := by
  have hn : 4 ≤ n := S.four_le
  cases hsl : S.slot r x with
  | block j =>
    by_cases hj : j = n
    · rw [S.label_block_E hsn hsl, if_pos hj] at hp
      have hgl : S.slot r (x + 1) = .gapL := S.step_of_block_n (hj ▸ hsl)
      by_cases hs : s = n
      · rw [S.label_gapL_W hsn hgl, if_pos hs] at hq
        getpq hp hq
        exact nfm_y1_z1
      · rw [S.label_gapL_W hsn hgl, if_neg hs] at hq
        getpq hp hq
        exact nfm_y1_b _
    · rw [S.label_block_E hsn hsl, if_neg hj] at hp
      exact absurd hp (by simp)
  | gapL =>
    by_cases hs : s = 0
    · rw [S.label_gapL_E hsn hsl, if_pos hs] at hp
      rcases S.succ_of_gapL hsl with hnext | hnext
      · rw [S.label_gapL_W hsn hnext, if_neg (by omega)] at hq
        getpq hp hq
        exact nfm_z2_b (by omega)
      · rw [S.label_gapR_W hsn hnext, if_neg (by omega)] at hq
        getpq hp hq
        exact nfm_z2_d (by omega)
    · rw [S.label_gapL_E hsn hsl, if_neg hs] at hp
      rcases S.succ_of_gapL hsl with hnext | hnext
      · by_cases hs' : s = n
        · rw [S.label_gapL_W hsn hnext, if_pos hs'] at hq
          getpq hp hq
          exact nfm_d_z1 _
        · rw [S.label_gapL_W hsn hnext, if_neg hs'] at hq
          getpq hp hq
          exact nfm_d_b _ _
      · by_cases hs' : s = n
        · rw [S.label_gapR_W hsn hnext, if_pos hs'] at hq
          getpq hp hq
          exact nfm_d_z2 (by omega)
        · rw [S.label_gapR_W hsn hnext, if_neg hs'] at hq
          getpq hp hq
          exact nfm_d_d _ _
  | gapR =>
    by_cases hs : s = 0
    · rw [S.label_gapR_E hsn hsl, if_pos hs] at hp
      rcases S.succ_of_gapR hsl with hnext | hnext
      · rw [S.label_gapR_W hsn hnext, if_neg (by omega)] at hq
        getpq hp hq
        exact nfm_z1_d _
      · rw [S.label_block_W hsn hnext, if_pos rfl] at hq
        getpq hp hq
        exact nfm_z1_y2
    · rw [S.label_gapR_E hsn hsl, if_neg hs] at hp
      rcases S.succ_of_gapR hsl with hnext | hnext
      · by_cases hs' : s = n
        · rw [S.label_gapR_W hsn hnext, if_pos hs'] at hq
          getpq hp hq
          exact nfm_b_z2 (by omega)
        · rw [S.label_gapR_W hsn hnext, if_neg hs'] at hq
          getpq hp hq
          exact nfm_b_d _ _
      · rw [S.label_block_W hsn hnext, if_pos rfl] at hq
        getpq hp hq
        exact nfm_b_y2 _

/-! ### The edges in the direction `NW`, inside a band -/

/-- No matched pair of edges in the direction `NW` between two cells of one band is
forbidden. -/
private lemma pairNWmid {r x : ℤ} {s : ℕ} (hsn : s + 1 ≤ n) {p q : StickEdge}
    (hp : S.toTiling.label (cellAt n r x s) HexDir.NW = some p)
    (hq : S.toTiling.label (cellAt n r x ((s + 1 : ℕ) : ℤ)) HexDir.SE = some q) :
    ¬ (markedRules n M).Forbidden p q := by
  have hn : 4 ≤ n := S.four_le
  cases hsl : S.slot r x with
  | block j =>
    have hjn : j ≤ n := S.block_le hsl
    by_cases hj : j = 0
    · rw [S.label_block_NW (by omega) hsl, if_pos hj] at hp
      rw [S.label_block_SE hsn hsl, if_neg (by omega)] at hq
      getpq hp hq
      exact nfm_x2_c _
    · rw [S.label_block_NW (by omega) hsl, if_neg hj] at hp
      by_cases hj' : j = n
      · rw [S.label_block_SE hsn hsl, if_pos hj'] at hq
        getpq hp hq
        exact nfm_a_x1 (by omega)
      · rw [S.label_block_SE hsn hsl, if_neg hj'] at hq
        getpq hp hq
        exact nfm_a_c _ _
  | gapL =>
    rw [S.label_gapL_NW (by omega) hsl, if_neg (by omega)] at hp
    exact absurd hp (by simp)
  | gapR =>
    rw [S.label_gapR_NW (by omega) hsl, if_neg (by omega)] at hp
    exact absurd hp (by simp)

/-! ### The edges in the direction `NW`, from one band to the next -/

/-- No matched pair of edges in the direction `NW` between two bands is forbidden, provided the
schematic respects the markings. -/
private lemma pairNWtop (hM : S.RespectsMarking M) {r x : ℤ} {p q : StickEdge}
    (hp : S.toTiling.label (cellAt n r x (n : ℕ)) HexDir.NW = some p)
    (hq : S.toTiling.label (cellAt n (r + 1) x (0 : ℕ)) HexDir.SE = some q) :
    ¬ (markedRules n M).Forbidden p q := by
  have hn : 4 ≤ n := S.four_le
  cases hsl : S.slot r x with
  | block j =>
    have hjn : j ≤ n := S.block_le hsl
    cases hsl' : S.slot (r + 1) x with
    | block j' =>
      have hj'n : j' ≤ n := S.block_le hsl'
      by_cases hj : j = 0
      · rw [S.label_block_NW le_rfl hsl, if_pos hj] at hp
        have hj' : j' ≠ n := by
          intro h
          exact absurd (S.block_bounds_of_block_n_above hsl (h ▸ hsl')).1 (by omega)
        rw [S.label_block_SE (by omega) hsl', if_neg hj'] at hq
        getpq hp hq
        exact nfm_x2_c _
      · rw [S.label_block_NW le_rfl hsl, if_neg hj] at hp
        by_cases hj' : j' = n
        · rw [S.label_block_SE (by omega) hsl', if_pos hj'] at hq
          obtain ⟨hb1, hb2⟩ := S.block_bounds_of_block_n_above hsl (hj' ▸ hsl')
          getpq hp hq
          exact nfm_a_x1_of hb1 hb2
            (hM.triangleR (j - 1) r x (by rw [hsl]; congr 1; omega) (hj' ▸ hsl'))
        · rw [S.label_block_SE (by omega) hsl', if_neg hj'] at hq
          getpq hp hq
          exact nfm_a_c _ _
    | gapL =>
      obtain ⟨hb1, hb2⟩ := S.block_bounds_of_gap_above (by rw [hsl']; trivial) hsl
      rw [S.label_block_NW le_rfl hsl, if_neg (by omega)] at hp
      rw [S.label_gapL_SE (by omega) hsl', if_pos rfl] at hq
      getpq hp hq
      refine nfm_a_y2_of (by omega) hb2 ?_
      intro hmem
      exact hM.topArrowL hmem r x (by rw [hsl]; congr 1; omega) hsl'
    | gapR =>
      obtain ⟨hb1, hb2⟩ := S.block_bounds_of_gap_above (by rw [hsl']; trivial) hsl
      rw [S.label_block_NW le_rfl hsl, if_neg (by omega)] at hp
      rw [S.label_gapR_SE (by omega) hsl', if_pos rfl] at hq
      getpq hp hq
      refine nfm_a_y1_of (by omega) hb2 ?_
      intro hmem
      exact hM.topArrowR hmem r x (by rw [hsl]; congr 1; omega) hsl'
  | gapL =>
    rw [S.label_gapL_NW le_rfl hsl, if_pos rfl] at hp
    cases hsl' : S.slot (r + 1) x with
    | block j' =>
      have hj'n : j' ≤ n := S.block_le hsl'
      have hj'0 : j' ≠ 0 := fun h => S.no_block_zero_above_gap (by rw [hsl]; trivial) (h ▸ hsl')
      have hj'N : j' ≠ n := fun h => S.no_block_n_above_gap (by rw [hsl]; trivial) (h ▸ hsl')
      rw [S.label_block_SE (by omega) hsl', if_neg hj'N] at hq
      getpq hp hq
      refine nfm_y1_c_of (by omega) ?_
      intro hmem
      exact hM.botArrowL hmem (r + 1) x hsl' (by simpa using hsl)
    | gapL =>
      exact (S.not_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim
    | gapR =>
      exact (S.not_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim
  | gapR =>
    rw [S.label_gapR_NW le_rfl hsl, if_pos rfl] at hp
    cases hsl' : S.slot (r + 1) x with
    | block j' =>
      have hj'n : j' ≤ n := S.block_le hsl'
      have hj'0 : j' ≠ 0 := fun h => S.no_block_zero_above_gap (by rw [hsl]; trivial) (h ▸ hsl')
      have hj'N : j' ≠ n := fun h => S.no_block_n_above_gap (by rw [hsl]; trivial) (h ▸ hsl')
      rw [S.label_block_SE (by omega) hsl', if_neg hj'N] at hq
      getpq hp hq
      refine nfm_y2_c_of (by omega) ?_
      intro hmem
      refine hM.botArrowR hmem (r + 1) x ?_ (by simpa using hsl)
      rw [hsl']; congr 1; omega
    | gapL =>
      exact (S.not_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim
    | gapR =>
      exact (S.not_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim

/-! ### The edges in the direction `NE` -/

/-- No matched pair of edges in the direction `NE` between two cells of one band is
forbidden. -/
private lemma pairNEmid {r x : ℤ} {s : ℕ} (hsn : s + 1 ≤ n) {p q : StickEdge}
    (hp : S.toTiling.label (cellAt n r x s) HexDir.NE = some p)
    (hq : S.toTiling.label (cellAt n r (x + 1) ((s + 1 : ℕ) : ℤ)) HexDir.SW = some q) :
    ¬ (markedRules n M).Forbidden p q := by
  have hn : 4 ≤ n := S.four_le
  cases hsl : S.slot r x with
  | block j =>
    have hjn : j ≤ n := S.block_le hsl
    by_cases hj : j = n
    · rw [S.label_block_NE (by omega) hsl, if_pos hj] at hp
      have hgl : S.slot r (x + 1) = .gapL := S.step_of_block_n (hj ▸ hsl)
      rw [S.label_gapL_SW hsn hgl, if_neg (by omega)] at hq
      getpq hp hq
      exact nfm_z1_a _
    · rw [S.label_block_NE (by omega) hsl, if_neg hj] at hp
      have hnext : S.slot r (x + 1) = .block (j + 1) := S.step_of_block_lt hsl (by omega)
      rw [S.label_block_SW hsn hnext, if_neg (by omega)] at hq
      getpq hp hq
      exact nfm_b_d _ _
  | gapL =>
    rw [S.label_gapL_NE (by omega) hsl, if_neg (by omega)] at hp
    rcases S.succ_of_gapL hsl with hnext | hnext
    · rw [S.label_gapL_SW hsn hnext, if_neg (by omega)] at hq
      getpq hp hq
      exact nfm_c_a _ _
    · rw [S.label_gapR_SW hsn hnext, if_neg (by omega)] at hq
      getpq hp hq
      exact nfm_c_c _ _
  | gapR =>
    rw [S.label_gapR_NE (by omega) hsl, if_neg (by omega)] at hp
    rcases S.succ_of_gapR hsl with hnext | hnext
    · rw [S.label_gapR_SW hsn hnext, if_neg (by omega)] at hq
      getpq hp hq
      exact nfm_a_c _ _
    · rw [S.label_block_SW hsn hnext, if_pos rfl] at hq
      getpq hp hq
      exact nfm_a_z2 _

/-- No matched pair of edges in the direction `NE` between two bands is forbidden, provided the
schematic respects the markings. -/
private lemma pairNEtop (hM : S.RespectsMarking M) {r x : ℤ} {p q : StickEdge}
    (hp : S.toTiling.label (cellAt n r x (n : ℕ)) HexDir.NE = some p)
    (hq : S.toTiling.label (cellAt n (r + 1) (x + 1) (0 : ℕ)) HexDir.SW = some q) :
    ¬ (markedRules n M).Forbidden p q := by
  have hn : 4 ≤ n := S.four_le
  cases hsl : S.slot r x with
  | block j =>
    have hjn : j ≤ n := S.block_le hsl
    cases hsl' : S.slot (r + 1) (x + 1) with
    | block j' =>
      have hj'n : j' ≤ n := S.block_le hsl'
      by_cases hj : j = n
      · rw [S.label_block_NE le_rfl hsl, if_pos hj] at hp
        have hj'0 : j' ≠ 0 := fun h =>
          S.no_diag_block_zero_above_block_n (hj ▸ hsl) (h ▸ hsl')
        rw [S.label_block_SW (by omega) hsl', if_neg hj'0] at hq
        getpq hp hq
        exact nfm_z1_d _
      · rw [S.label_block_NE le_rfl hsl, if_neg hj] at hp
        by_cases hj' : j' = 0
        · rw [S.label_block_SW (by omega) hsl', if_pos hj'] at hq
          getpq hp hq
          by_cases hj0 : j = 0
          · exact nfm_b_z2 (by omega)
          · refine nfm_b_z2_of (by omega) ?_
            have htri := hM.triangleL (j - 1) r x (by rw [hsl]; congr 1; omega) (hj' ▸ hsl')
            rwa [show n - 1 - (n - j) = j - 1 by omega]
        · rw [S.label_block_SW (by omega) hsl', if_neg hj'] at hq
          getpq hp hq
          exact nfm_b_d _ _
    | gapL =>
      have hj : j ≠ n := fun h =>
        S.no_diag_gap_above_block_n (h ▸ hsl) (by rw [hsl']; trivial)
      rw [S.label_block_NE le_rfl hsl, if_neg hj] at hp
      rw [S.label_gapL_SW (by omega) hsl', if_pos rfl] at hq
      getpq hp hq
      exact nfm_b_x2 _
    | gapR =>
      have hj : j ≠ n := fun h =>
        S.no_diag_gap_above_block_n (h ▸ hsl) (by rw [hsl']; trivial)
      rw [S.label_block_NE le_rfl hsl, if_neg hj] at hp
      rw [S.label_gapR_SW (by omega) hsl', if_pos rfl] at hq
      getpq hp hq
      exact nfm_b_x1 _
  | gapL =>
    rw [S.label_gapL_NE le_rfl hsl, if_pos rfl] at hp
    cases hsl' : S.slot (r + 1) (x + 1) with
    | block j' =>
      have hj'0 : j' ≠ 0 := fun h =>
        S.no_diag_block_zero_above_gap (by rw [hsl]; trivial) (h ▸ hsl')
      rw [S.label_block_SW (by omega) hsl', if_neg hj'0] at hq
      getpq hp hq
      exact nfm_x1_d _
    | gapL =>
      exact (S.no_diag_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim
    | gapR =>
      exact (S.no_diag_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim
  | gapR =>
    rw [S.label_gapR_NE le_rfl hsl, if_pos rfl] at hp
    cases hsl' : S.slot (r + 1) (x + 1) with
    | block j' =>
      have hj'0 : j' ≠ 0 := fun h =>
        S.no_diag_block_zero_above_gap (by rw [hsl]; trivial) (h ▸ hsl')
      rw [S.label_block_SW (by omega) hsl', if_neg hj'0] at hq
      getpq hp hq
      exact nfm_x2_d _
    | gapL =>
      exact (S.no_diag_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim
    | gapR =>
      exact (S.no_diag_gap_above_gap (by rw [hsl]; trivial) (by rw [hsl']; trivial)).elim

/-! ### The correspondence -/

/-- If a schematic respects its markings, the tiling it describes satisfies the marked rules. -/
theorem toTiling_satisfiesRules_of_respectsMarking (hM : S.RespectsMarking M) :
    S.toTiling.SatisfiesRules (markedRules n M) := by
  refine StickTiling.satisfiesRules_of_three _ _ ?_
  intro c e p q he hp hq
  rw [labelOf_markedRules] at hp hq
  obtain ⟨r, x, s, hsn, rfl⟩ := exists_cellAt (n := n) c
  rcases he with rfl | rfl | rfl
  · rw [nbr_cellAt_E, show HexDir.E.opp = HexDir.W from by decide] at hq
    exact S.pairE M hsn hp hq
  · rw [nbr_cellAt_NE, show HexDir.NE.opp = HexDir.SW from by decide] at hq
    by_cases hs : s = n
    · rw [hs] at hp hq
      rw [cellAt_top_nat] at hq
      exact S.pairNEtop M hM hp hq
    · rw [show ((s : ℤ) + 1) = ((s + 1 : ℕ) : ℤ) by push_cast; ring] at hq
      exact S.pairNEmid M (by omega) hp hq
  · rw [nbr_cellAt_NW, show HexDir.NW.opp = HexDir.SE from by decide] at hq
    by_cases hs : s = n
    · rw [hs] at hp hq
      rw [cellAt_top_nat] at hq
      exact S.pairNWtop M hM hp hq
    · rw [show ((s : ℤ) + 1) = ((s + 1 : ℕ) : ℤ) by push_cast; ring] at hq
      exact S.pairNWmid M (by omega) hp hq

/-- If the tiling described by a schematic satisfies the marked rules, then the schematic
respects its markings. -/
theorem respectsMarking_of_toTiling_satisfiesRules
    (hv : S.toTiling.SatisfiesRules (markedRules n M)) : S.RespectsMarking M := by
  have hn : 4 ≤ n := S.four_le
  constructor
  · -- left-facing arrow marks on the top
    intro i hi r x hb hg
    have hle : i + 1 ≤ n := S.block_le hb
    have hp : S.toTiling.label (cellAt n r x (n : ℕ)) HexDir.NW = some (.a (n - i)) := by
      rw [S.label_block_NW le_rfl hb, if_neg (by omega)]
      congr 2
      omega
    have hq : S.toTiling.label (nbr (cellAt n r x (n : ℕ)) HexDir.NW) HexDir.NW.opp
        = some .y2 := by
      rw [nbr_cellAt_NW, cellAt_top_nat, show HexDir.NW.opp = HexDir.SE from by decide,
        S.label_gapL_SE (by omega) hg, if_pos rfl]
    rw [← labelOf_markedRules M] at hp hq
    exact hv _ _ _ _ hp hq (Or.inr (Or.inl (MarkForbiddenCore.topArrowL (by omega) hi rfl rfl)))
  · -- right-facing arrow marks on the top
    intro i hi r x hb hg
    have hle : i + 2 ≤ n := S.block_le hb
    have hp : S.toTiling.label (cellAt n r x (n : ℕ)) HexDir.NW = some (.a (n - i - 1)) := by
      rw [S.label_block_NW le_rfl hb, if_neg (by omega)]
      congr 2
      omega
    have hq : S.toTiling.label (nbr (cellAt n r x (n : ℕ)) HexDir.NW) HexDir.NW.opp
        = some .y1 := by
      rw [nbr_cellAt_NW, cellAt_top_nat, show HexDir.NW.opp = HexDir.SE from by decide,
        S.label_gapR_SE (by omega) hg, if_pos rfl]
    rw [← labelOf_markedRules M] at hp hq
    exact hv _ _ _ _ hp hq (Or.inr (Or.inl (MarkForbiddenCore.topArrowR (by omega) hi rfl rfl)))
  · -- left-facing arrow marks on the bottom
    intro i hi r x hb hg
    have hle : i ≤ n := S.block_le hb
    have hin : i ≠ n := by
      intro h
      refine S.no_block_n_above_gap (r := r - 1) (by rw [hg]; trivial) ?_
      rw [show r - 1 + 1 = r by ring, hb, h]
    have hp : S.toTiling.label (cellAt n (r - 1) x (n : ℕ)) HexDir.NW = some .y1 := by
      rw [S.label_gapL_NW le_rfl hg, if_pos rfl]
    have hq : S.toTiling.label (nbr (cellAt n (r - 1) x (n : ℕ)) HexDir.NW) HexDir.NW.opp
        = some (.c (i + 1)) := by
      rw [nbr_cellAt_NW, cellAt_top_nat, show HexDir.NW.opp = HexDir.SE from by decide,
        show r - 1 + 1 = r by ring, S.label_block_SE (by omega) hb, if_neg hin]
    rw [← labelOf_markedRules M] at hp hq
    exact hv _ _ _ _ hp hq (Or.inr (Or.inr (MarkForbiddenCore.botArrowL (by omega) hi rfl rfl)))
  · -- right-facing arrow marks on the bottom
    intro i hi r x hb hg
    have hle : i + 1 ≤ n := S.block_le hb
    have hin : i + 1 ≠ n := by
      intro h
      refine S.no_block_n_above_gap (r := r - 1) (by rw [hg]; trivial) ?_
      rw [show r - 1 + 1 = r by ring, hb, h]
    have hp : S.toTiling.label (cellAt n (r - 1) x (n : ℕ)) HexDir.NW = some .y2 := by
      rw [S.label_gapR_NW le_rfl hg, if_pos rfl]
    have hq : S.toTiling.label (nbr (cellAt n (r - 1) x (n : ℕ)) HexDir.NW) HexDir.NW.opp
        = some (.c (i + 2)) := by
      rw [nbr_cellAt_NW, cellAt_top_nat, show HexDir.NW.opp = HexDir.SE from by decide,
        show r - 1 + 1 = r by ring, S.label_block_SE (by omega) hb, if_neg hin]
    rw [← labelOf_markedRules M] at hp hq
    exact hv _ _ _ _ hp hq (Or.inr (Or.inr (MarkForbiddenCore.botArrowR (by omega) hi rfl rfl)))
  · -- right-facing triangle marks
    intro i r x hb hb'
    by_contra hmem
    obtain ⟨hc1, hc2⟩ := S.block_bounds_of_block_n_above hb hb'
    have hp : S.toTiling.label (cellAt n r x (n : ℕ)) HexDir.NW = some (.a (n - i)) := by
      rw [S.label_block_NW le_rfl hb, if_neg (by omega)]
      congr 2
      omega
    have hq : S.toTiling.label (nbr (cellAt n r x (n : ℕ)) HexDir.NW) HexDir.NW.opp
        = some .x1 := by
      rw [nbr_cellAt_NW, cellAt_top_nat, show HexDir.NW.opp = HexDir.SE from by decide,
        S.label_block_SE (by omega) hb', if_pos rfl]
    rw [← labelOf_markedRules M] at hp hq
    exact hv _ _ _ _ hp hq
      (Or.inr (Or.inl (MarkForbiddenCore.triangleR (by omega) hmem rfl rfl)))
  · -- left-facing triangle marks
    intro i r x hb hb'
    by_contra hmem
    have hgR : S.slot (r + 1) x = .gapR := by
      have := S.gapR_of_block_zero hb'
      rwa [show x + 1 - 1 = x by ring] at this
    obtain ⟨hc1, hc2⟩ := S.block_bounds_of_gap_above (by rw [hgR]; trivial) hb
    have hp : S.toTiling.labelOf (markedRules n M) (cellAt n r x (n : ℕ)) HexDir.NE
        = some (.b (n - 1 - i)) := by
      rw [labelOf_markedRules, S.label_block_NE le_rfl hb, if_neg (by omega)]
      congr 2
      omega
    have hq : S.toTiling.labelOf (markedRules n M) (nbr (cellAt n r x (n : ℕ)) HexDir.NE)
        HexDir.NE.opp = some .z2 := by
      rw [labelOf_markedRules, nbr_cellAt_NE, cellAt_top_nat,
        show HexDir.NE.opp = HexDir.SW from by decide,
        S.label_block_SW (by omega) hb', if_pos rfl]
      rfl
    exact hv _ _ _ _ hp hq
      (Or.inr (Or.inl (MarkForbiddenCore.triangleL (by omega) hmem rfl rfl)))

/-- **The tiling described by a schematic satisfies the marked rules exactly when the schematic
respects the markings.** -/
theorem toTiling_satisfiesRules_iff :
    S.toTiling.SatisfiesRules (markedRules n M) ↔ S.RespectsMarking M :=
  ⟨S.respectsMarking_of_toTiling_satisfiesRules M, S.toTiling_satisfiesRules_of_respectsMarking M⟩

/-- The marking with no arrow marks and all triangle marks: it forbids nothing beyond the eleven
rules of the paper. -/
def plainMarking (n : ℕ) : Marking n where
  topArrowL := ∅
  topArrowR := ∅
  botArrowL := ∅
  botArrowR := ∅
  triangleL := Set.univ
  triangleR := Set.univ

/-- Every schematic respects the marking with no arrows and all triangles. -/
lemma respectsMarking_plainMarking : S.RespectsMarking (plainMarking n) where
  topArrowL := by intro i hi; exact absurd hi (by simp [plainMarking])
  topArrowR := by intro i hi; exact absurd hi (by simp [plainMarking])
  botArrowL := by intro i hi; exact absurd hi (by simp [plainMarking])
  botArrowR := by intro i hi; exact absurd hi (by simp [plainMarking])
  triangleR := by intro i r x _ _; trivial
  triangleL := by intro i r x _ _; trivial

/-- **The tiling described by a schematic satisfies the eleven matching rules of the paper.**
Together with `Schematic.toTiling_isWeavePattern` this shows that every schematic describes a
genuine valid tiling. -/
theorem toTiling_satisfiesWeaveRules : S.toTiling.SatisfiesWeaveRules := by
  intro c e p q hp hq hf
  exact S.toTiling_satisfiesRules_of_respectsMarking (plainMarking n)
    S.respectsMarking_plainMarking c e p q hp hq (Or.inl hf)

end Schematic

end StickPolyhex
