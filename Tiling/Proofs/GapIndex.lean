import Tiling.Proofs.GapAssignment

/-!
# Indexing the gaps of a schematic

The combinatorial data `GapAssignment G` of `Tiling/Proofs/GapAssignment.lean` records a state
for every row and two values for every gap, the gaps of each row being indexed by `ℤ` from left
to right *coherently between adjacent rows*: the `k`-th gap of the row `r` has to lie above the
block of the row `r - 1` bounded by the gaps `k` and `k + 1` of that row.

This file produces such an indexing for an arbitrary schematic.  The gaps of a schematic form a
type `Schematic.GapPt S`, carrying two commuting permutations:

* `Schematic.GapPt.nextE`, moving to the next gap of the same row;
* `Schematic.GapPt.downE`, moving to the gap of the row below which ends below the given gap.

Both are bijections (`Schematic.GapPt.next_bijective`, `Schematic.GapPt.down_bijective`) and they
commute (`Schematic.GapPt.down_next`), so the group `ℤ²` acts on the gaps and a single gap of the
row `0` gives the required indexing `Schematic.gapOf`.
-/

namespace StickPolyhex

namespace Schematic

variable {n : ℕ}

/-- A gap of the schematic `S`: a row together with the column at which the gap starts. -/
structure GapPt (S : Schematic n) where
  /-- The row of the schematic in which the gap lies. -/
  row : ℤ
  /-- The first column of the gap. -/
  col : ℤ
  /-- The columns from `col` on really do form a gap of the row `row`. -/
  gap_exists : ∃ l m : ℕ, S.GapAt row col l m

namespace GapPt

variable {S : Schematic n}

lemma eq_of_row_col {p q : GapPt S} (hr : p.row = q.row) (hc : p.col = q.col) : p = q := by
  cases p; cases q; simp_all

/-- The length of the left part of the gap. -/
noncomputable def lenL (p : GapPt S) : ℕ := p.gap_exists.choose

/-- The length of the right part of the gap. -/
noncomputable def lenR (p : GapPt S) : ℕ := p.gap_exists.choose_spec.choose

lemma gapAt (p : GapPt S) : S.GapAt p.row p.col p.lenL p.lenR :=
  p.gap_exists.choose_spec.choose_spec

lemma lenL_eq {p : GapPt S} {l m : ℕ} (h : S.GapAt p.row p.col l m) : p.lenL = l :=
  (GapAt.unique p.gapAt h).1

lemma lenR_eq {p : GapPt S} {l m : ℕ} (h : S.GapAt p.row p.col l m) : p.lenR = m :=
  (GapAt.unique p.gapAt h).2

/-- The first column of the block following the gap. -/
noncomputable def endCol (p : GapPt S) : ℤ := p.col + p.lenL + p.lenR

lemma lt_endCol (p : GapPt S) : p.col < p.endCol := by
  have := p.gapAt.l_pos
  have := p.gapAt.m_pos
  simp only [endCol]
  omega

lemma slot_endCol (p : GapPt S) : S.slot p.row p.endCol = .block 0 := p.gapAt.blockRight

/-- Two gaps of the same row which end at the same column are equal. -/
lemma eq_of_endCol_eq {p q : GapPt S} (hr : p.row = q.row) (h : p.endCol = q.endCol) : p = q := by
  refine eq_of_row_col hr ?_
  have hp := p.gapAt
  have hq := q.gapAt
  rw [hr] at hp
  have hpl := p.gapAt.l_pos
  have hpm := p.gapAt.m_pos
  have hql := q.gapAt.l_pos
  have hqm := q.gapAt.m_pos
  simp only [endCol] at h
  rcases lt_trichotomy p.col q.col with hlt | heq | hgt
  · exfalso
    have := gap_gap_gap hp hq hlt
    omega
  · exact heq
  · exfalso
    have := gap_gap_gap hq hp hgt
    omega

/-! ### The next gap of a row -/

lemma exists_next (p : GapPt S) : ∃ l m : ℕ, S.GapAt p.row (p.endCol + n + 1) l m :=
  exists_right_gap p.slot_endCol

/-- The gap following `p` in its row. -/
noncomputable def next (p : GapPt S) : GapPt S :=
  ⟨p.row, p.endCol + n + 1, p.exists_next⟩

@[simp] lemma next_row (p : GapPt S) : (p.next).row = p.row := rfl

@[simp] lemma next_col (p : GapPt S) : (p.next).col = p.endCol + n + 1 := rfl

lemma next_injective : Function.Injective (next (S := S)) := by
  intro p q h
  have hr : p.row = q.row := by
    have := congrArg GapPt.row h
    simpa using this
  have hc : p.endCol = q.endCol := by
    have := congrArg GapPt.col h
    simp only [next_col] at this
    omega
  exact eq_of_endCol_eq hr hc

lemma next_surjective : Function.Surjective (next (S := S)) := by
  intro q
  have hblock : S.slot q.row (q.col - 1) = .block n := q.gapAt.blockLeft
  have hzero : S.slot q.row (q.col - 1 - n) = .block 0 := by
    have := S.slot_block_zero hblock
    simpa using this
  obtain ⟨u, l, m, hgap, hsum⟩ := exists_left_gap hzero
  refine ⟨⟨q.row, u, ⟨l, m, hgap⟩⟩, ?_⟩
  refine eq_of_row_col rfl ?_
  have hl : (⟨q.row, u, ⟨l, m, hgap⟩⟩ : GapPt S).lenL = l := lenL_eq hgap
  have hm : (⟨q.row, u, ⟨l, m, hgap⟩⟩ : GapPt S).lenR = m := lenR_eq hgap
  simp only [next_col, endCol, hl, hm]
  omega

lemma next_bijective : Function.Bijective (next (S := S)) :=
  ⟨next_injective, next_surjective⟩

/-! ### The gap of the row below -/

lemma exists_j (p : GapPt S) : ∃ j, S.GapData p.row p.col p.lenL p.lenR j :=
  exists_gapData p.gapAt

/-- The index, inside the block of the row below on which it lies, of the first column of the
gap. -/
noncomputable def jOf (p : GapPt S) : ℕ := p.exists_j.choose

lemma gapData (p : GapPt S) : S.GapData p.row p.col p.lenL p.lenR p.jOf := p.exists_j.choose_spec

lemma jOf_eq {p : GapPt S} {j : ℕ} (h : S.slot (p.row - 1) p.col = .block j) : p.jOf = j := by
  have h1 := p.gapData.slot_below
  rw [h] at h1
  injection h1 with e
  exact e.symm

/-- The first column of the block of the row below on which the gap lies. -/
noncomputable def belowCol (p : GapPt S) : ℤ := p.col - p.jOf

lemma slot_belowCol (p : GapPt S) : S.slot (p.row - 1) p.belowCol = .block 0 :=
  S.slot_block_zero p.gapData.slot_below

lemma exists_down (p : GapPt S) :
    ∃ (u : ℤ) (l m : ℕ), S.GapAt (p.row - 1) u l m ∧ u + l + m = p.belowCol :=
  exists_left_gap p.slot_belowCol

/-- The gap of the row below which ends just below the gap `p`, i.e. which ends at the first
column of the block on which `p` lies. -/
noncomputable def down (p : GapPt S) : GapPt S where
  row := p.row - 1
  col := p.exists_down.choose
  gap_exists := by
    obtain ⟨l, m, h, -⟩ := p.exists_down.choose_spec
    exact ⟨l, m, h⟩

@[simp] lemma down_row (p : GapPt S) : (p.down).row = p.row - 1 := rfl

@[simp] lemma down_endCol (p : GapPt S) : (p.down).endCol = p.belowCol := by
  obtain ⟨l, m, h, he⟩ := p.exists_down.choose_spec
  have hl : (p.down).lenL = l := lenL_eq (p := p.down) h
  have hm : (p.down).lenR = m := lenR_eq (p := p.down) h
  simp only [endCol, hl, hm]
  exact he

lemma down_injective : Function.Injective (down (S := S)) := by
  intro p q h
  have hr : p.row = q.row := by
    have := congrArg GapPt.row h
    simp only [down_row] at this
    omega
  have hb : p.belowCol = q.belowCol := by
    rw [← down_endCol, ← down_endCol, h]
  have hp2 := p.gapData.two_le
  have hq2 := q.gapData.two_le
  have hpb := p.gapData.bound
  have hqb := q.gapData.bound
  have hpl := p.gapAt.l_pos
  have hpm := p.gapAt.m_pos
  have hql := q.gapAt.l_pos
  have hqm := q.gapAt.m_pos
  simp only [belowCol] at hb
  refine eq_of_row_col hr ?_
  rcases lt_trichotomy p.col q.col with hlt | heq | hgt
  · exfalso
    have hgq : S.GapAt p.row q.col q.lenL q.lenR := by rw [hr]; exact q.gapAt
    have := gap_gap_gap p.gapAt hgq hlt
    push_cast at hpb hqb ⊢
    omega
  · exact heq
  · exfalso
    have hgq : S.GapAt p.row q.col q.lenL q.lenR := by rw [hr]; exact q.gapAt
    have := gap_gap_gap hgq p.gapAt hgt
    push_cast at hpb hqb ⊢
    omega

lemma down_surjective : Function.Surjective (down (S := S)) := by
  intro w
  obtain ⟨g, hg1, hg2, hgap⟩ := S.exists_gap_above_block w.slot_endCol
  obtain ⟨u, l, m, hgapAt, hu1, hu2⟩ := exists_gapAt_of_isGap hgap
  refine ⟨⟨w.row + 1, u, ⟨l, m, hgapAt⟩⟩, ?_⟩
  set p : GapPt S := ⟨w.row + 1, u, ⟨l, m, hgapAt⟩⟩ with hp
  have hprow : p.row = w.row + 1 := rfl
  have hpcol : p.col = u := rfl
  have hl : p.lenL = l := lenL_eq (p := p) hgapAt
  have hm : p.lenR = m := lenR_eq (p := p) hgapAt
  have hge : w.endCol ≤ u := by
    by_contra hcon
    push_neg at hcon
    have h1 : (S.slot (w.row + 1) (w.endCol - 1)).IsGap :=
      hgapAt.isGap (by omega) (by omega)
    have h2 : (S.slot w.row (w.endCol - 1)).IsGap :=
      w.gapAt.isGap (by have := w.lt_endCol; simp only [endCol] at *; omega)
        (by simp only [endCol] at *; omega)
    exact S.not_isGap_above_of_isGap h2 h1
  have hle : u ≤ w.endCol + n := by omega
  have hblock : S.slot w.row u = .block (u - w.endCol).toNat :=
    S.slot_of_start w.slot_endCol hge hle
  have hj : p.jOf = (u - w.endCol).toNat := by
    refine jOf_eq (p := p) ?_
    rw [hprow, hpcol, show w.row + 1 - 1 = w.row by ring]
    exact hblock
  refine eq_of_endCol_eq (by simp [hprow]) ?_
  rw [down_endCol]
  simp only [belowCol, hpcol, hj]
  omega

lemma down_bijective : Function.Bijective (down (S := S)) :=
  ⟨down_injective, down_surjective⟩

/-- Moving to the next gap of a row and moving one row down commute. -/
lemma down_next (p : GapPt S) : (p.next).down = (p.down).next := by
  have hc : S.slot p.row p.endCol = .block 0 := p.slot_endCol
  have hg₁ : S.GapData p.row p.col p.lenL p.lenR p.jOf := p.gapData
  have he₁ : p.col + p.lenL + p.lenR = p.endCol := rfl
  have hg₂ : S.GapData p.row (p.endCol + n + 1) (p.next).lenL (p.next).lenR (p.next).jOf := by
    have := (p.next).gapData
    simpa using this
  obtain ⟨l', m', hgap', hsum'⟩ := below_gap hc hg₁ he₁ hg₂
  have hcol : (p.down).next.col = p.col - p.jOf + n + 1 := by
    simp only [next_col, down_endCol, belowCol]
  have hrow : (p.down).next.row = p.row - 1 := rfl
  have hgap'' : S.GapAt ((p.down).next).row ((p.down).next).col l' m' := by
    rw [hrow, hcol]
    exact hgap'
  refine (eq_of_endCol_eq ?_ ?_).symm
  · simp only [hrow, down_row, next_row]
  · have hl : ((p.down).next).lenL = l' := lenL_eq hgap''
    have hm : ((p.down).next).lenR = m' := lenR_eq hgap''
    rw [down_endCol]
    simp only [endCol, hl, hm, hcol, belowCol, next_col]
    omega

/-! ### The two commuting permutations -/

/-- Moving to the next gap of a row, as a permutation of the gaps of the schematic. -/
noncomputable def nextE : Equiv.Perm (GapPt S) := Equiv.ofBijective _ next_bijective

/-- Moving one row down, as a permutation of the gaps of the schematic. -/
noncomputable def downE : Equiv.Perm (GapPt S) := Equiv.ofBijective _ down_bijective

@[simp] lemma nextE_apply (p : GapPt S) : nextE p = p.next := rfl

@[simp] lemma downE_apply (p : GapPt S) : downE p = p.down := rfl

lemma commute_downE_nextE : Commute (downE (S := S)) (nextE (S := S)) := by
  ext p
  simp only [Equiv.Perm.mul_apply, nextE_apply, downE_apply]
  exact down_next p

lemma row_downE_zpow (z : ℤ) : ∀ p : GapPt S, ((downE ^ z) p).row = p.row - z := by
  induction z using Int.induction_on with
  | zero => simp
  | succ j ih =>
    intro p
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, downE_apply, down_row]
    ring
  | pred j ih =>
    intro p
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    have : (downE (S := S)) ((downE (S := S))⁻¹ p) = p := by simp
    rw [downE_apply] at this
    have hr := congrArg GapPt.row this
    rw [down_row] at hr
    omega

lemma row_nextE_zpow (z : ℤ) : ∀ p : GapPt S, ((nextE ^ z) p).row = p.row := by
  induction z using Int.induction_on with
  | zero => simp
  | succ j ih =>
    intro p
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, nextE_apply, next_row]
  | pred j ih =>
    intro p
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    have : (nextE (S := S)) ((nextE (S := S))⁻¹ p) = p := by simp
    rw [nextE_apply] at this
    have hr := congrArg GapPt.row this
    rw [next_row] at hr
    omega

end GapPt

/-! ### A coherent indexing of the gaps -/

variable (S : Schematic n)

lemma exists_gapPt_zero : ∃ p : GapPt S, p.row = 0 := by
  obtain ⟨x, hx⟩ := S.exists_gap 0
  obtain ⟨u, l, m, hgap, -, -⟩ := exists_gapAt_of_isGap hx
  exact ⟨⟨0, u, ⟨l, m, hgap⟩⟩, rfl⟩

/-- A gap of the row `0`, used as the origin of the indexing of the gaps. -/
noncomputable def baseGap : GapPt S := (exists_gapPt_zero S).choose

lemma baseGap_row : (baseGap S).row = 0 := (exists_gapPt_zero S).choose_spec

/-- The `k`-th gap of the row `r`: the gaps of each row are indexed by `ℤ` from left to right, in
such a way that the `k`-th gap of the row `r` lies above the block of the row `r - 1` bounded by
the gaps `k` and `k + 1` of that row. -/
noncomputable def gapOf (r k : ℤ) : GapPt S :=
  (GapPt.downE ^ (-r)) ((GapPt.nextE ^ k) (baseGap S))

@[simp] lemma gapOf_row (r k : ℤ) : (gapOf S r k).row = r := by
  rw [gapOf, GapPt.row_downE_zpow, GapPt.row_nextE_zpow, baseGap_row]
  ring

lemma gapOf_down (r k : ℤ) : (gapOf S r k).down = gapOf S (r - 1) k := by
  rw [gapOf, gapOf, show -(r - 1) = 1 + -r by ring, zpow_add, zpow_one,
    Equiv.Perm.mul_apply, GapPt.downE_apply]

lemma gapOf_next (r k : ℤ) : (gapOf S r k).next = gapOf S r (k + 1) := by
  have hcomm : (GapPt.downE (S := S) ^ (-r)) * GapPt.nextE
      = GapPt.nextE * (GapPt.downE (S := S) ^ (-r)) :=
    (GapPt.commute_downE_nextE.zpow_left (-r)).eq
  rw [gapOf, gapOf, show k + 1 = 1 + k by ring, zpow_add, zpow_one,
    Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply (GapPt.downE ^ (-r)) GapPt.nextE, hcomm,
    Equiv.Perm.mul_apply, GapPt.nextE_apply]

/-- The gap data of the `k`-th gap of the row `r`. -/
lemma gapData_gapOf (r k : ℤ) :
    S.GapData r (gapOf S r k).col (gapOf S r k).lenL (gapOf S r k).lenR (gapOf S r k).jOf := by
  have := (gapOf S r k).gapData
  rwa [gapOf_row] at this

/-- The `k`-th gap of the row `r - 1` ends at the first column of the block on which the `k`-th
gap of the row `r` lies. -/
lemma gapOf_endCol_below (r k : ℤ) :
    (gapOf S (r - 1) k).col + (gapOf S (r - 1) k).lenL + (gapOf S (r - 1) k).lenR
      = (gapOf S r k).col - (gapOf S r k).jOf := by
  have := GapPt.down_endCol (gapOf S r k)
  rw [gapOf_down] at this
  exact this

/-- The `(k+1)`-st gap of the row `r - 1` starts just after the block on which the `k`-th gap of
the row `r` lies. -/
lemma gapOf_col_succ_below (r k : ℤ) :
    (gapOf S (r - 1) (k + 1)).col = (gapOf S r k).col - (gapOf S r k).jOf + n + 1 := by
  rw [← gapOf_next, GapPt.next_col, GapPt.endCol, gapOf_endCol_below]


/-! ### From the gap conditions to a gap assignment -/

section Assignment

variable {G : GapSpec} {S : Schematic G.blockLen} {st : ℤ → ℕ}

/-- The combinatorial data attached to a schematic satisfying the gap conditions: the state of
each row, and the two values of the `k`-th gap of each row for the indexing `gapOf`. -/
noncomputable def toGapAssignment (h : S.GapConditions G st) : GapAssignment G where
  st := st
  xv r k := G.lval (st (r - 1)) (gapOf S r k).lenL
  yv r k := G.rval (st (r - 1)) (gapOf S r k).lenR
  state_mem := h.state_mem
  state_cycle := h.state_cycle
  x_mem r k := h.left_value r _ _ _ _ (gapData_gapOf S r k)
  y_mem r k := h.right_value r _ _ _ _ (gapData_gapOf S r k)
  value_sum r k := by
    have hZ : S.GapData (r - 1)
        ((gapOf S r k).col - (gapOf S r k).jOf + G.blockLen + 1)
        (gapOf S (r - 1) (k + 1)).lenL (gapOf S (r - 1) (k + 1)).lenR
        (gapOf S (r - 1) (k + 1)).jOf := by
      have := gapData_gapOf S (r - 1) (k + 1)
      rwa [gapOf_col_succ_below] at this
    have hkey := h.value_sum (gapData_gapOf S r k) (gapData_gapOf S (r - 1) k)
      (gapOf_endCol_below S r k) hZ
    rw [show r - 1 - 1 = r - 2 by ring]
    exact hkey
  interval r k := by
    have hkey := h.interval r _ _ _ _ (gapData_gapOf S r k) _ _ _ _
      (gapData_gapOf S (r - 1) k) (gapOf_endCol_below S r k)
    rw [show r - 1 - 1 = r - 2 by ring]
    exact hkey

/-- **Every schematic satisfying the gap conditions provides a gap assignment**: its gaps can be
indexed coherently from row to row, and the resulting states and values satisfy the conditions of
`GapAssignment`. -/
theorem nonempty_gapAssignment_of_satisfiesGapConditions (h : S.SatisfiesGapConditions G) :
    Nonempty (GapAssignment G) := by
  obtain ⟨st, hst⟩ := h
  exact ⟨toGapAssignment hst⟩

end Assignment

end Schematic

end StickPolyhex
