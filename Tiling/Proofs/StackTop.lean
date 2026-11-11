import Tiling.Proofs.BottomRow

/-!
# The structure of the row above a left-leaning stack

Using the local steps of `Tiling/Proofs/TopRow.lean`, this file determines the whole row of
cells lying on the back side of the topmost stick of a left-leaning stack: reading the row from
the far end towards the near end one meets first the horizontal stick filling the space `A`,
then the ends of the left-slanting sticks of a vertical stack, and finally a *second* horizontal
stick, which fills the space `B` of the paper.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### The cells of the row above a stick -/

/-- The `j`-th cell of the row lying on the back side of the stick through `x` (for a stick of
direction `u`): the cell just above the `j`-th cell of that stick. -/
def upCell (u : HexDir) (x : Hex) (j : ℕ) : Hex := nbr (walk (T.head x) u j) (u + 5)

/-- A cell of the row above a stack which is the end of a left-slanting stick: either the last
cell of a stick of direction `u + 2` or the first cell of a stick of direction `u + 5`. -/
def SlantEndAbove (u : HexDir) (z : Hex) : Prop :=
  (T.dir z = u + 2 ∧ T.idx z = n) ∨ (T.dir z = u + 5 ∧ T.idx z = 1)

lemma walk_nat_succ (c : Hex) (d : HexDir) (j : ℕ) :
    walk c d ((j + 1 : ℕ) : ℤ) = nbr (walk c d (j : ℤ)) d := by
  have := walk_succ c d (j : ℤ)
  push_cast
  simpa using this

lemma upCell_succ (u : HexDir) (x : Hex) (j : ℕ) :
    T.upCell u x (j + 1) = nbr (T.upCell u x j) u := by
  simp only [upCell, walk_nat_succ, nbr]
  abel

lemma upCell_pred (u : HexDir) (x : Hex) (j : ℕ) :
    nbr (T.upCell u x (j + 1)) (u + 3) = T.upCell u x j := by
  rw [T.upCell_succ]
  exact nbr_nbr_cancel _ (opp_eq_add_three u).symm

lemma upCell_zero (u : HexDir) (x : Hex) : T.upCell u x 0 = nbr (T.head x) (u + 5) := by
  simp [upCell, walk]

/-- The cells of the stick through `x` itself, in the form used by the row analysis. -/
lemma dir_idx_rowBase {u : HexDir} {x : Hex} (hdx : T.dir x = u) {j : ℕ} (hj : j < n) :
    T.dir (walk (T.head x) u (j : ℤ)) = u ∧ T.idx (walk (T.head x) u (j : ℤ)) = j + 1 := by
  have hd : T.dir (T.head x) = u := by rw [T.dir_head x, hdx]
  have h := T.dir_walk_forward (T.head x) j (by rw [T.idx_head x]; omega)
  rw [hd, T.idx_head x] at h
  exact ⟨h.1, by omega⟩

lemma upCell_tail {u : HexDir} {x : Hex} (hdx : T.dir x = u) :
    T.upCell u x (n - 1) = nbr (T.tail x) (u + 5) := by
  have : T.tail x = walk (T.head x) u ((n - 1 : ℕ) : ℤ) := by
    rw [tail, cellOfStick, hdx]
  rw [upCell, this]

/-- Walking along the row. -/
lemma upCell_walk (u : HexDir) (x : Hex) (j : ℕ) (k : ℤ) (l : ℕ) (h : (j : ℤ) + k = (l : ℤ)) :
    walk (T.upCell u x j) u k = T.upCell u x l := by
  simp only [upCell, walk, nbr, ← h, add_smul]
  abel

/-! ### Descending along the row -/

/-- **The row above a stack, from the vertical stack to the second horizontal stack.**  If the
`m`-th cell of the row is the last cell of a left-slanting stick of direction `u + 2`, then
somewhere before it the row reaches the far end of a horizontal stick, and in between it
consists of ends of left-slanting sticks. -/
lemma top_row_descend (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {x : Hex} {u : HexDir}
    (hdx : T.dir x = u) {m : ℕ} (hm : m + 1 < n)
    (hbase : T.dir (T.upCell u x m) = u + 2 ∧ T.idx (T.upCell u x m) = n) :
    ∃ s : ℕ, s < m ∧ T.dir (T.upCell u x s) = u ∧ T.idx (T.upCell u x s) = n ∧
      ∀ j, s < j → j ≤ m → T.SlantEndAbove u (T.upCell u x j) := by
  have hdh : T.dir (T.head x) = u := by rw [T.dir_head x, hdx]
  -- the local step of the analysis
  have step : ∀ j, j + 1 ≤ m → T.SlantEndAbove u (T.upCell u x (j + 1)) →
      (1 ≤ j ∧ T.SlantEndAbove u (T.upCell u x j)) ∨
        (T.dir (T.upCell u x j) = u ∧ T.idx (T.upCell u x j) = n) := by
    intro j hj hs
    obtain ⟨hdp, hip⟩ := T.dir_idx_rowBase hdx (show j < n by omega)
    have hpn : T.idx (walk (T.head x) u (j : ℤ)) < n := by omega
    have hnbr : nbr (walk (T.head x) u (j : ℤ)) u = walk (T.head x) u ((j + 1 : ℕ) : ℤ) :=
      (walk_nat_succ (T.head x) u j).symm
    rcases hs with ⟨hd2, hi2⟩ | ⟨hd5, hi5⟩
    · have hstep := T.top_step_two hv hn hdp hpn (by rw [hnbr]; exact hd2)
        (by rw [hnbr]; exact hi2)
      exact Or.inl ⟨by omega, hstep.2⟩
    · have hstep := T.top_step_five hv hn hdp hpn (by rw [hnbr]; exact hd5)
        (by rw [hnbr]; exact hi5)
      rcases hstep with ⟨h2, hd, hi⟩ | ⟨hd, hi⟩
      · exact Or.inl ⟨by omega, Or.inr ⟨hd, hi⟩⟩
      · exact Or.inr ⟨hd, hi⟩
  -- descending induction along the row
  have W : ∀ k : ℕ, k ≤ m →
      ((∀ i, m - k ≤ i → i ≤ m → T.SlantEndAbove u (T.upCell u x i)) ∨
        (∃ s, m - k ≤ s ∧ s ≤ m ∧ T.dir (T.upCell u x s) = u ∧ T.idx (T.upCell u x s) = n ∧
          ∀ i, s < i → i ≤ m → T.SlantEndAbove u (T.upCell u x i))) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine Or.inl fun i hi hi' => ?_
      have : i = m := by omega
      subst this
      exact Or.inl hbase
    | succ k ih =>
      intro hk
      rcases ih (by omega) with hall | ⟨s, hs1, hs2, hs3, hs4, hs5⟩
      · have hj : (m - (k + 1)) + 1 = m - k := by omega
        have hslant : T.SlantEndAbove u (T.upCell u x ((m - (k + 1)) + 1)) := by
          rw [hj]; exact hall (m - k) (le_refl _) (by omega)
        rcases step (m - (k + 1)) (by omega) hslant with ⟨h1, h2⟩ | ⟨hd, hi⟩
        · refine Or.inl fun i hi hi' => ?_
          rcases Nat.eq_or_lt_of_le hi with rfl | hlt
          · exact h2
          · exact hall i (by omega) hi'
        · exact Or.inr ⟨m - (k + 1), le_refl _, by omega, hd, hi, fun i hi hi' =>
            hall i (by omega) hi'⟩
      · exact Or.inr ⟨s, by omega, hs2, hs3, hs4, hs5⟩
  rcases W m (le_refl m) with hall | ⟨s, _, hs2, hs3, hs4, hs5⟩
  · exfalso
    have h0 : T.SlantEndAbove u (T.upCell u x 0) := hall 0 (by omega) (by omega)
    rw [T.upCell_zero] at h0
    exact T.top_no_slant_head hv hn hdh (T.idx_head x) h0
  · refine ⟨s, ?_, hs3, hs4, hs5⟩
    rcases Nat.eq_or_lt_of_le hs2 with rfl | hlt
    · exact absurd (hs3.symm.trans hbase.1) ((by decide : ∀ a : HexDir, ¬ (a = a + 2)) u)
    · exact hlt


/-! ### The whole row above the topmost stick -/

/-- The base of the row analysis (Figure 15): the cell of the row just in front of the head of
the horizontal stick filling the space `A` is the last cell of a stick of direction `u + 2`. -/
lemma top_row_base (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (hi1 : 1 < T.idx (nbr (T.tail x) (u + 5))) (hin : T.idx (nbr (T.tail x) (u + 5)) < n) :
    T.dir (T.upCell u x (n - T.idx (nbr (T.tail x) (u + 5)) - 1)) = u + 2 ∧
      T.idx (T.upCell u x (n - T.idx (nbr (T.tail x) (u + 5)) - 1)) = n := by
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have hdA : T.dir (nbr (T.tail x) (u + 5)) = u :=
    (T.dir_backCorner_beyond_tail hv (by omega) hL hu hx).1
  have hkey := T.dir_eastCell_head_of_backCorner hv hn hL hu hx hdA hi1 hin
  set A := nbr (T.tail x) (u + 5) with hA
  set i := T.idx A with hi
  have hle : i ≤ n := T.idx_le A
  have hAup : T.upCell u x (n - 1) = A := T.upCell_tail hdx
  have hheadA : T.head A = T.upCell u x (n - i) := by
    rw [head, hdA, ← hi, ← hAup]
    refine T.upCell_walk u x (n - 1) (-((i : ℤ) - 1)) (n - i) ?_
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : i ≤ n)]
    push_cast
    ring
  rw [hheadA, show n - i = (n - i - 1) + 1 from by omega, T.upCell_pred] at hkey
  exact hkey

/-- **The row of cells above the topmost stick of a left-leaning stack.**  Let `x` be a stick of
a left-leaning stack of direction `u` whose space `A` is filled by a new horizontal stick.  Then
the row of cells on the back side of `x` consists, from the near end, of the cells of a second
horizontal stick, whose far end is the `s`-th cell of the row, then of the ends of left-slanting
sticks, and finally of the cells of the stick filling `A`. -/
theorem top_row_structure (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (hi1 : 1 < T.idx (nbr (T.tail x) (u + 5))) (hin : T.idx (nbr (T.tail x) (u + 5)) < n) :
    ∃ s : ℕ, s + 2 ≤ n ∧
      T.dir (T.upCell u x s) = u ∧ T.idx (T.upCell u x s) = n ∧
      T.dir (T.upCell u x (s + 1)) = u + 5 ∧ T.idx (T.upCell u x (s + 1)) = 1 ∧
      ∀ j, s < j → j < n → T.SlantEndAbove u (T.upCell u x j) ∨
        T.upCell u x j ∈ T.stickOf (nbr (T.tail x) (u + 5)) := by
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  have hdA : T.dir (nbr (T.tail x) (u + 5)) = u :=
    (T.dir_backCorner_beyond_tail hv (by omega) hL hu hx).1
  have hbase := T.top_row_base hv hn hL hu hx hi1 hin
  set A := nbr (T.tail x) (u + 5) with hA
  set i := T.idx A with hi
  have hle : i ≤ n := T.idx_le A
  have hAup : T.upCell u x (n - 1) = A := T.upCell_tail hdx
  have hheadA : T.head A = T.upCell u x (n - i) := by
    rw [head, hdA, ← hi, ← hAup]
    refine T.upCell_walk u x (n - 1) (-((i : ℤ) - 1)) (n - i) ?_
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : i ≤ n)]
    push_cast
    ring
  obtain ⟨s, hsm, hds, his, hslant⟩ := T.top_row_descend hv (by omega) hdx
    (m := n - i - 1) (by omega) hbase
  have hfive : T.dir (T.upCell u x (s + 1)) = u + 5 ∧ T.idx (T.upCell u x (s + 1)) = 1 := by
    -- the cell one step further along the row is the head of a stick of direction `u + 5`
    rcases hslant (s + 1) (by omega) (by omega) with ⟨hd2, hi2⟩ | ⟨hd5, hi5⟩
    · exfalso
      obtain ⟨hdp, hip⟩ := T.dir_idx_rowBase hdx (show s < n by omega)
      have hnbr : nbr (walk (T.head x) u (s : ℤ)) u = walk (T.head x) u ((s + 1 : ℕ) : ℤ) :=
        (walk_nat_succ (T.head x) u s).symm
      have hstep := T.top_step_two hv (by omega) hdp (by omega) (by rw [hnbr]; exact hd2)
        (by rw [hnbr]; exact hi2)
      rcases hstep.2 with ⟨hd, -⟩ | ⟨hd, -⟩
      · exact absurd (hds.symm.trans hd) ((by decide : ∀ a : HexDir, ¬ (a = a + 2)) u)
      · exact absurd (hds.symm.trans hd) ((by decide : ∀ a : HexDir, ¬ (a = a + 5)) u)
    · exact ⟨hd5, hi5⟩
  refine ⟨s, by omega, hds, his, hfive.1, hfive.2, ?_⟩
  · intro j hj hjn
    by_cases hjm : j ≤ n - i - 1
    · exact Or.inl (hslant j hj hjm)
    · refine Or.inr ?_
      rw [T.mem_stickOf_iff A (T.upCell u x j)]
      refine ⟨j - (n - i), by omega, ?_⟩
      rw [cellOfStick, hdA, hheadA]
      refine T.upCell_walk u x (n - i) ((j - (n - i) : ℕ) : ℤ) j ?_
      rw [Nat.cast_sub (by omega : n - i ≤ j)]
      ring


/-! ### The second stack above -/

/-- The stick whose far end is the `s`-th cell of the row lies in a left-leaning stack: it ends
side by side with the stick filling the next concave corner of the left-slanting stick beyond
it. -/
lemma isLeftLeaningStack_upCell (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {x : Hex} {u : HexDir} {s : ℕ}
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n)
    (hd5 : T.dir (T.upCell u x (s + 1)) = u + 5) (hi5 : T.idx (T.upCell u x (s + 1)) = 1) :
    T.IsLeftLeaningStack (T.upCell u x s) := by
  have hp4 : nbr (T.upCell u x (s + 1)) (T.dir (T.upCell u x (s + 1)) + 4) = T.upCell u x s := by
    rw [hd5, (by decide : ∀ a : HexDir, a + 5 + 4 = a + 3) u]
    exact T.upCell_pred u x s
  have hend : T.EndsAt (nbr (T.upCell u x (s + 1)) (T.dir (T.upCell u x (s + 1)) + 4))
      (T.dir (T.upCell u x (s + 1)) + 1) := by
    rw [hp4, hd5, add_five_one u]
    exact Or.inl ⟨hds, his⟩
  have hpair := T.leansLeft_of_endsAt_corner hv hn (p := T.upCell u x (s + 1))
    (by rw [hi5]; omega) hend
  rw [hp4] at hpair
  exact ⟨T.upCell u x s, _, T.sameStack_refl _, hpair⟩

/-- The cells of the row before the `s`-th one all belong to the stick whose far end it is. -/
lemma upCell_mem_stickOf_of_le {x : Hex} {u : HexDir} {s j : ℕ}
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n)
    (hsn : s + 1 ≤ n) (hjs : j ≤ s) : T.upCell u x j ∈ T.stickOf (T.upCell u x s) := by
  rw [T.mem_stickOf_iff]
  refine ⟨n - 1 - s + j, by omega, ?_⟩
  rw [cellOfStick, head, hds, his, walk_walk]
  exact T.upCell_walk u x s _ j (by omega)

/-- The cell diagonally beyond the near end of the stick, on its back side, also belongs to that
stick. -/
lemma backCorner_head_mem_stickOf {x : Hex} {u : HexDir} {s : ℕ}
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n) (hsn : s + 2 ≤ n) :
    nbr (T.head x) (u + 4) ∈ T.stickOf (T.upCell u x s) := by
  have hvec : (u + 4).vec = (u + 5).vec - u.vec := by
    have := vec_four_zero u
    rw [← this]
    abel
  rw [T.mem_stickOf_iff]
  refine ⟨n - s - 2, by omega, ?_⟩
  rw [cellOfStick, head, hds, his, walk_walk,
    show -((n : ℤ) - 1) + ((n - s - 2 : ℕ) : ℤ) = -(s : ℤ) - 1 from by omega]
  simp only [upCell, walk, nbr, hvec]
  module

/-- The cell of the row that is the far end of a stick is that stick's own far end. -/
lemma tail_upCell {x : Hex} {u : HexDir} {s : ℕ} (hn : 0 < n)
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n) :
    T.tail (T.upCell u x s) = T.upCell u x s := by
  rw [T.tail_eq_walk hn, hds, his]
  simp

lemma frontCell_upCell {x : Hex} {u : HexDir} {s : ℕ} (hn : 0 < n)
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n) :
    T.frontCell u (T.upCell u x s) = T.upCell u x (s + 1) := by
  rw [frontCell, endCell, if_pos hds, T.tail_upCell hn hds his, T.upCell_succ]

/-- The second stack above a left-leaning stack is a different stack. -/
lemma not_sameStack_upCell (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex} {u : HexDir} {s : ℕ}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n) (hsn : s + 2 ≤ n) :
    ¬ T.SameStack c (T.upCell u x s) := by
  intro hsame
  have h0n : 0 < n := by omega
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx, hu]
  have hax0 : SameAxis u (T.dir c) := Or.inl hu
  -- the cells beyond the far ends of the two sticks lie on the stick flanking the stack
  have hmem := (T.frontCell_mem_of_sameStack hv h0n hax0 hsame).2
  have hmemx := (T.frontCell_mem_of_sameStack hv h0n hax0 hx).2
  have hfx : T.frontCell u x = nbr (T.tail x) u := by rw [frontCell, endCell, if_pos hdx]
  have hdF : T.dir (T.frontCell u c) = u + 5 := by
    have h1 := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl c)).1
    rw [hu] at h1
    rw [frontCell, endCell, if_pos hu]
    exact h1
  rw [hfx] at hmemx
  rw [T.frontCell_upCell h0n hds his] at hmem
  obtain ⟨k, hk⟩ := T.exists_walk_of_mem_stickOf hmem hmemx
  rw [hdF] at hk
  -- comparing the two cells gives a contradiction
  have htx : T.tail x = walk (T.head x) u ((n - 1 : ℕ) : ℤ) := by rw [tail, cellOfStick, hdx]
  have hkey : (((s : ℤ) + 1) - n) • u.vec = (k - 1) • (u + 5).vec := by
    rw [htx, show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 from by omega] at hk
    simp only [upCell, walk, nbr] at hk
    push_cast at hk
    linear_combination (norm := module) hk
  obtain ⟨h1, -⟩ := smul_vec_eq_smul_vec ((by decide : ∀ a : HexDir, a ≠ a + 5) u)
    (by rw [opp_add_five]; exact (by decide : ∀ a : HexDir, a ≠ a + 2) u) hkey
  omega

/-- The second stack above a left-leaning stack is different from the first one. -/
lemma not_sameStack_backCorner_upCell (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {x : Hex} {u : HexDir}
    {s : ℕ} (hLA : T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)))
    (hdA : T.dir (nbr (T.tail x) (u + 5)) = u) (hdx : T.dir x = u)
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n) (hsn : s + 2 ≤ n) :
    ¬ T.SameStack (nbr (T.tail x) (u + 5)) (T.upCell u x s) := by
  intro hsame
  have h0n : 0 < n := by omega
  obtain ⟨i, hi⟩ : ∃ i, T.idx (nbr (T.tail x) (u + 5)) = i := ⟨_, rfl⟩
  have hile : i ≤ n := hi ▸ T.idx_le _
  have hA : nbr (T.tail x) (u + 5) = T.upCell u x (n - 1) := (T.upCell_tail hdx).symm
  have hax0 : SameAxis u (T.dir (nbr (T.tail x) (u + 5))) := Or.inl hdA
  have hmem := (T.frontCell_mem_of_sameStack hv h0n hax0 hsame).2
  have hdFA : T.dir (T.frontCell u (nbr (T.tail x) (u + 5))) = u + 5 := by
    have h1 := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hLA (T.sameStack_refl _)).1
    rw [hdA] at h1
    rw [frontCell, endCell, if_pos hdA]
    exact h1
  have hfA : T.frontCell u (nbr (T.tail x) (u + 5)) = T.upCell u x (2 * n - i) := by
    rw [frontCell, endCell, if_pos hdA, T.tail_eq_walk h0n, hdA, hi, nbr_eq_walk_one, walk_walk,
      hA]
    exact T.upCell_walk u x (n - 1) _ (2 * n - i) (by omega)
  rw [T.frontCell_upCell h0n hds his, hfA] at hmem
  obtain ⟨k, hk⟩ := T.exists_walk_of_mem_stickOf hmem (T.self_mem_stickOf _)
  rw [hfA] at hdFA
  rw [hdFA] at hk
  have hkey : (((s : ℤ) + 1) - (2 * (n : ℤ) - i)) • u.vec = k • (u + 5).vec := by
    simp only [upCell, walk, nbr] at hk
    rw [show ((2 * n - i : ℕ) : ℤ) = 2 * (n : ℤ) - i from by omega] at hk
    push_cast at hk
    linear_combination (norm := module) hk
  obtain ⟨h1, -⟩ := smul_vec_eq_smul_vec ((by decide : ∀ a : HexDir, a ≠ a + 5) u)
    (by rw [opp_add_five]; exact (by decide : ∀ a : HexDir, a ≠ a + 2) u) hkey
  omega


/-- **Every left-leaning stack has (at least) two left-leaning stacks above it.**  A left-leaning
stack of horizontal sticks of direction `u` has, on its back side, two *different* left-leaning
stacks of horizontal sticks of the same direction: the stack filling the space `A` beyond the
far ends of its sticks, and the stack filling the space `B` beyond their near ends.  This is
Figures 13 to 17 of the paper. -/
theorem exists_two_stackAbove (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ a₁ a₂ : Hex, T.dir a₁ = u ∧ T.IsLeftLeaningStack a₁ ∧ T.StackAbove u c a₁ ∧
      T.dir a₂ = u ∧ T.IsLeftLeaningStack a₂ ∧ T.StackAbove u c a₂ ∧ ¬ T.SameStack a₁ a₂ := by
  have h0n : 0 < n := by omega
  obtain ⟨x, hx, hne⟩ := T.exists_backCorner_not_sameStack hv (by omega) hL hu
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv (by omega) hL hx, hu]
  obtain ⟨hdA, hcase⟩ := T.dir_backCorner_beyond_tail hv (by omega) hL hu hx
  obtain ⟨hi1, hin⟩ : 1 < T.idx (nbr (T.tail x) (u + 5)) ∧ T.idx (nbr (T.tail x) (u + 5)) < n := by
    rcases hcase with ⟨-, hsame⟩ | h
    · exact absurd hsame hne
    · exact h
  have hLA : T.IsLeftLeaningStack (nbr (T.tail x) (u + 5)) := by
    rcases T.isLeftLeaningStack_backCorner hv hn hL hu hx with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨s, hs2, hds, his, hd5, hi5, hrow⟩ := T.top_row_structure hv hn hL hu hx hi1 hin
  refine ⟨nbr (T.tail x) (u + 5), T.upCell u x s, hdA, hLA, ⟨hne, T.tail x, ?_, ?_⟩, hds,
    T.isLeftLeaningStack_upCell hv (by omega) hds his hd5 hi5,
    ⟨T.not_sameStack_upCell hv (by omega) hL hu hx hds his hs2, T.head x, ?_, ?_⟩,
    T.not_sameStack_backCorner_upCell hv (by omega) hLA hdA hdx hds his hs2⟩
  · exact SameStack.trans T hx
      (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n x)).symm)
  · exact Or.inr (T.sameStack_refl _)
  · exact SameStack.trans T hx
      (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.head_mem_stickOf x)).symm)
  · refine Or.inr ?_
    rw [← T.upCell_zero]
    exact T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem
      (T.upCell_mem_stickOf_of_le hds his (by omega) (Nat.zero_le s))).symm

end StickTiling

end StickPolyhex
