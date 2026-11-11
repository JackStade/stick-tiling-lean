import Tiling.Proofs.Corners

/-!
# Left-leaning stacks

This file proves the two facts of Lemma 4 of the paper about *left-leaning* stacks:

* `exists_isLeftLeaningStack`: a valid tiling always contains a left-leaning stack;
* `stackHeight_eq_of_isLeftLeaningStack`: a left-leaning stack contains exactly `n` sticks.

A stack is left-leaning when the stacked pairs occurring in it lean left (by
`leansLeft_iff_of_sameStack` this does not depend on the pair chosen).
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Sticks that end at a given cell -/

/-- A stick which ends at `y` in the direction `m` consists of the `n` cells obtained from `y`
by walking in the direction `m + 3` (i.e. away from the end). -/
lemma stickOf_head {c : Hex} (hc : T.idx c = 1) :
    T.stickOf c = (Finset.range n).image (fun k : ℕ => walk c (T.dir c) k) := by
  rw [T.stickOf_eq_image_walk c, show T.head c = c from by rw [head, hc]; norm_num]

/-- A stick which ends at `y` in the direction `m` consists of the `n` cells obtained from `y`
by walking in the direction `m + 3` (i.e. away from the end). -/
lemma stickOf_of_endsAt {y : Hex} {m : HexDir} (h : T.EndsAt y m) :
    T.stickOf y = (Finset.range n).image (fun k : ℕ => walk y (m + 3) k) := by
  rw [T.stickOf_eq_image_walk y]
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · have hhead : T.head y = walk y m (-((n : ℤ) - 1)) := by rw [head, hd, hi]
    have hstep : ∀ k : ℕ, k < n →
        walk (T.head y) (T.dir y) (k : ℤ) = walk y (m + 3) ((n - 1 - k : ℕ) : ℤ) := by
      intro k hk
      rw [hhead, hd, walk_walk, show m + 3 = m.opp from rfl, walk_opp]
      congr 1
      have : ((n - 1 - k : ℕ) : ℤ) = (n : ℤ) - 1 - k := by omega
      omega
    refine Finset.ext fun x => ?_
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨n - 1 - k, by omega, (hstep k hk).symm⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨n - 1 - j, by omega, ?_⟩
      rw [hstep (n - 1 - j) (by omega)]
      congr 2
      omega
  · have hhead : T.head y = y := by
      rw [head, hi]
      norm_num
    rw [hhead, hd, show m.opp = m + 3 from rfl]

/-- Two sticks ending at neighbouring cells in the direction `m` (the neighbour being taken in
the direction `m + 5`, along the line of the ends) form a left-leaning stacked pair. -/
lemma leansLeft_of_endsAt_pair {u : HexDir} {y : Hex} (h : T.EndsAt y (u + 1))
    (h' : T.EndsAt (nbr y u) (u + 1)) : T.LeansLeft y (nbr y u) := by
  have hdy : T.dir y = u + 1 ∨ T.dir y = u + 4 := by
    rcases h with ⟨hd, _⟩ | ⟨hd, _⟩
    · exact Or.inl hd
    · exact Or.inr (by rw [hd, opp_add_one])
  have hdy' : T.dir (nbr y u) = u + 1 ∨ T.dir (nbr y u) = u + 4 := by
    rcases h' with ⟨hd, _⟩ | ⟨hd, _⟩
    · exact Or.inl hd
    · exact Or.inr (by rw [hd, opp_add_one])
  have hs1 := T.stickOf_of_endsAt h
  have hs2 := T.stickOf_of_endsAt h'
  refine ⟨u, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (by decide : ∀ a b : HexDir, (b = a + 1 ∨ b = a + 4) → ¬ SameAxis b a) u (T.dir y) hdy
  · exact (by decide : ∀ a b c : HexDir, (b = a + 1 ∨ b = a + 4) → (c = a + 1 ∨ c = a + 4) →
      SameAxis b c) u (T.dir y) (T.dir (nbr y u)) hdy hdy'
  · intro x hx
    rw [hs1] at hx
    rw [hs2]
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨k, hk, ?_⟩
    simp only [walk, nbr]
    abel
  · exact (by decide : ∀ a b : HexDir, (b = a + 1 ∨ b = a + 4) → (a = b + 2 ∨ a = b + 5))
      u (T.dir y) hdy

/-- If the back corner of a cell `p` of a stick is the end of another stick, then that stick and
its neighbour along the next back corner form a left-leaning pair. -/
theorem leansLeft_of_endsAt_corner (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p : Hex} (hp : T.idx p < n)
    (h : T.EndsAt (nbr p (T.dir p + 4)) (T.dir p + 1)) :
    T.LeansLeft (nbr p (T.dir p + 4)) (nbr p (T.dir p + 5)) := by
  have hnb : nbr (nbr p (T.dir p + 4)) (T.dir p) = nbr p (T.dir p + 5) :=
    nbr_nbr_of_vec p (vec_four_zero _)
  have h' : T.EndsAt (nbr p (T.dir p + 5)) (T.dir p + 1) := by
    rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
    · obtain ⟨hd', hi'⟩ := T.corner_step_forward_A hv hn hp hd hi
      exact Or.inl ⟨hd', hi'⟩
    · rw [opp_add_one] at hd
      obtain ⟨hd', hi'⟩ := T.corner_step_forward_B hv hn hp hd hi
      exact Or.inr ⟨by rw [hd', opp_add_one], hi'⟩
  have := T.leansLeft_of_endsAt_pair h (by rw [hnb]; exact h')
  rwa [hnb] at this

/-! ### The two sticks of a left-leaning pair are parallel -/

/-- Rules 6 and 8: the two sticks of a left-leaning stacked pair carry their arrows the same
way, i.e. they have the same direction (and not just the same axis). -/
theorem dir_eq_of_leansLeft (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c c' : Hex} (h : T.LeansLeft c c') :
    T.dir c' = T.dir c := by
  obtain ⟨e, hst, he⟩ := h
  rcases hst.2.1 with hd | hd
  · exact hd
  have hd3 : T.dir c' = T.dir c + 3 := by rw [hd, opp_eq_add_three]
  have hne3 : ∀ a : HexDir, a + 3 ≠ a := by decide
  exfalso
  rcases he with he | he
  · -- the pair is stacked towards `dir c + 2`: use the head of the stick
    subst he
    set h0 := T.head c with hh0
    have hdh : T.dir h0 = T.dir c := T.dir_head c
    have hih : T.idx h0 = 1 := T.idx_head c
    have hmem : nbr h0 (T.dir c + 2) ∈ T.stickOf c' := hst.2.2 h0 (T.head_mem_stickOf c)
    have hdh' : T.dir (nbr h0 (T.dir c + 2)) = T.dir c + 3 := by
      rw [T.dir_of_mem_stickOf hmem, hd3]
    have hend := T.endsAt_nbr_of_stackedBy_head
      (StackedBy.of_mem_stickOf T hst (T.head_mem_stickOf c)) hih
    have hih' : T.idx (nbr h0 (T.dir c + 2)) = n := by
      rcases hend with ⟨_, hi⟩ | ⟨hdd, _⟩
      · exact hi
      · exact absurd (by rw [← hdh', hdd, HexDir.opp_opp, hdh] : T.dir c + 3 = T.dir c)
          (hne3 (T.dir c))
    have hx1 : T.label h0 (T.dir c + 2) = some .x1 := by
      rw [show T.dir c + 2 = T.dir h0 + 2 by rw [hdh], T.label_dir_add_two, if_pos hih]
    have hcc : T.label (nbr h0 (T.dir c + 2)) (T.dir c + 2).opp = some (.c 1) := by
      rw [opp_add_two,
        T.label_shift2 (u := T.dir c) (k := 3) (by rw [hdh']) (by decide : (5 : HexDir) = 3 + 2),
        if_neg (by omega), hih', show n + 1 - n = 1 from by omega]
    exact T.clash hv hx1 hcc (Or.inl (ForbiddenCore.rule6 (le_refl 1) (by omega)))
  · -- the pair is stacked towards `dir c + 5`: use the tail of the stick
    subst he
    set t := T.tail c with ht
    have hdt : T.dir t = T.dir c := T.dir_tail (by omega) c
    have hit : T.idx t = n := T.idx_tail (by omega) c
    have hmem : nbr t (T.dir c + 5) ∈ T.stickOf c' := hst.2.2 t (T.tail_mem_stickOf (by omega) c)
    have hdt' : T.dir (nbr t (T.dir c + 5)) = T.dir c + 3 := by
      rw [T.dir_of_mem_stickOf hmem, hd3]
    have hend := T.endsAt_nbr_of_stackedBy_tail
      (StackedBy.of_mem_stickOf T hst (T.tail_mem_stickOf (by omega) c)) hit
    have hit' : T.idx (nbr t (T.dir c + 5)) = 1 := by
      rcases hend with ⟨hdd, _⟩ | ⟨_, hi⟩
      · exact absurd (by rw [← hdt', hdd, hdt] : T.dir c + 3 = T.dir c) (hne3 (T.dir c))
      · exact hi
    have hx2 : T.label t (T.dir c + 5) = some .x2 := by
      rw [show T.dir c + 5 = T.dir t + 5 by rw [hdt], T.label_dir_add_five, if_pos hit]
    have haa : T.label (nbr t (T.dir c + 5)) (T.dir c + 5).opp = some (.a 1) := by
      rw [opp_add_five,
        T.label_shift5 (u := T.dir c) (k := 3) (by rw [hdt']) (by decide : (2 : HexDir) = 3 + 5),
        if_neg (by omega), hit']
    exact T.clash hv hx2 haa (Or.inl (ForbiddenCore.rule8 (le_refl 1) (by omega)))

/-! ### Left-leaning stacks -/

/-- A stack is *left-leaning* if it contains a stacked pair that leans left.  By
`leansLeft_iff_of_sameStack` all the stacked pairs of such a stack lean left. -/
def IsLeftLeaningStack (c : Hex) : Prop := ∃ a b, T.SameStack c a ∧ T.LeansLeft a b

/-- The height of a stack: the number of sticks it contains. -/
noncomputable def stackHeight (c : Hex) : ℕ := (T.Stack c).ncard

/-! ### Existence of a left-leaning stack -/

/-- In a tiling with no left-leaning pair, every stick has a partner stick directly beside it,
namely its translate by one step in the direction `dir c + 4`. -/
lemma aligned_partner_of_no_leansLeft (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n)
    (hL : ∀ a b : Hex, ¬ T.LeansLeft a b) {c : Hex} (hc : T.idx c = 1) :
    T.dir (nbr c (T.dir c + 4)) = T.dir c ∧ T.idx (nbr c (T.dir c + 4)) = 1 := by
  have hcn : T.idx c < n := by omega
  rcases T.backCorner_head hv (by omega) hc with hpar | hend
  · set v := nbr c (T.dir c + 5) with hvdef
    have hposv := T.idx_pos v
    have hlev := T.idx_le v
    rcases lt_trichotomy (T.idx v) 2 with hm | hm | hm
    · -- `v` is the head of a stick parallel to that of `c`: a left-leaning pair
      exfalso
      have hm1 : T.idx v = 1 := by omega
      refine hL c v ⟨T.dir c + 5, ⟨?_, ?_, ?_⟩, Or.inr rfl⟩
      · exact (by decide : ∀ a : HexDir, ¬ SameAxis a (a + 5)) (T.dir c)
      · exact Or.inl hpar
      · intro x hx
        rw [T.stickOf_head hc] at hx
        rw [T.stickOf_head hm1]
        simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
        obtain ⟨k, hk, rfl⟩ := hx
        refine ⟨k, hk, ?_⟩
        rw [hpar]
        simp only [walk, nbr, hvdef]
        abel
    · -- `v` is the second cell of the aligned partner stick
      have hvopp : (T.dir v).opp = T.dir c + 3 := by rw [hpar, opp_eq_add_three]
      have hnb : nbr v (T.dir c + 3) = nbr c (T.dir c + 4) := nbr_nbr_of_vec c (vec_five_three _)
      constructor
      · rw [← hnb, ← hvopp, T.pred_dir v (by omega), hpar]
      · rw [← hnb, ← hvopp, T.pred_idx v (by omega)]
        omega
    · -- the stick through `v` ends before the end of the stick through `c`
      exfalso
      obtain ⟨hdp, hip⟩ := T.dir_walk_forward c (n - T.idx v + 1) (by omega)
      set p := walk c (T.dir c) ((n - T.idx v + 1 : ℕ) : ℤ) with hpdef
      have hipn : T.idx p = n - T.idx v + 2 := by rw [hip, hc]; omega
      obtain ⟨hdq, hiq⟩ := T.dir_walk_forward v (n - T.idx v) (by omega)
      have hqeq : nbr (nbr p (T.dir p + 5)) (T.dir p + 3)
          = walk v (T.dir v) ((n - T.idx v : ℕ) : ℤ) := by
        rw [hdp, hpar, hpdef, hvdef]
        simp only [walk, nbr, vec_add_three]
        push_cast [show n - T.idx v + 1 = (n - T.idx v) + 1 from rfl]
        simp only [add_smul, one_smul]
        abel
      have hq1 : T.dir (nbr (nbr p (T.dir p + 5)) (T.dir p + 3)) = T.dir p := by
        rw [hqeq, hdq, hpar, hdp]
      have hq2 : T.idx (nbr (nbr p (T.dir p + 5)) (T.dir p + 3)) = n := by
        rw [hqeq, hiq]; omega
      obtain ⟨hdz, hiz⟩ := T.corner_beyond_tail hv (p := p) (by omega) hq1 hq2
      set z := nbr p (T.dir p + 5) with hzdef
      have harith : T.dir z + 4 = T.dir p + 3 := by
        rw [hdz]; exact (by decide : ∀ a : HexDir, a + 5 + 4 = a + 3) _
      have hend2 : T.EndsAt (nbr z (T.dir z + 4)) (T.dir z + 1) := by
        refine Or.inl ⟨?_, ?_⟩
        · rw [harith, hq1, hdz]
          exact (by decide : ∀ a : HexDir, a = a + 5 + 1) _
        · rw [harith]; exact hq2
      exact hL _ _ (T.leansLeft_of_endsAt_corner hv (by omega) (by omega : T.idx z < n) hend2)
  · -- the back corner at the head is the end of a stick: a left-leaning pair again
    exfalso
    have hd2 : T.dir (nbr c (T.dir c)) = T.dir c := T.succ_dir c hcn
    have hi2 : T.idx (nbr c (T.dir c)) = 2 := by rw [T.succ_idx c hcn, hc]
    have hnb : nbr (nbr c (T.dir c)) (T.dir c + 4) = nbr c (T.dir c + 5) :=
      nbr_nbr_of_vec c (vec_zero_four _)
    refine hL _ _ (T.leansLeft_of_endsAt_corner hv (by omega) (p := nbr c (T.dir c))
      (by omega) ?_)
    rw [hd2, hnb]
    exact hend

/-- **Every valid tiling contains a left-leaning stack.** -/
theorem exists_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 3 ≤ n) :
    ∃ c : Hex, T.IsLeftLeaningStack c := by
  by_contra hcon
  push_neg at hcon
  have hL : ∀ a b : Hex, ¬ T.LeansLeft a b := fun a b hab =>
    hcon a ⟨a, b, T.sameStack_refl a, hab⟩
  obtain ⟨c0, hic0⟩ : ∃ c0 : Hex, T.idx c0 = 1 := ⟨T.head (0, 0), T.idx_head _⟩
  have hfsucc : ∀ k : ℕ, walk c0 (T.dir c0 + 4) ((k + 1 : ℕ) : ℤ)
      = nbr (walk c0 (T.dir c0 + 4) (k : ℤ)) (T.dir c0 + 4) := by
    intro k
    rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring, walk_succ]
  have hstep : ∀ k : ℕ, T.dir (walk c0 (T.dir c0 + 4) (k : ℤ)) = T.dir c0 ∧
      T.idx (walk c0 (T.dir c0 + 4) (k : ℤ)) = 1 := by
    intro k
    induction k with
    | zero => simpa using hic0
    | succ k ih =>
      obtain ⟨hdk, hik⟩ := ih
      have hal := T.aligned_partner_of_no_leansLeft hv hn hL hik
      rw [hdk] at hal
      rw [hfsucc k]
      exact hal
  have hpair : ∀ k : ℕ, T.IsStackedPair (walk c0 (T.dir c0 + 4) (k : ℤ))
      (walk c0 (T.dir c0 + 4) ((k + 1 : ℕ) : ℤ)) := by
    intro k
    obtain ⟨hdk, hik⟩ := hstep k
    obtain ⟨hdk', hik'⟩ := hstep (k + 1)
    refine ⟨T.dir c0 + 4, ?_, ?_, ?_⟩
    · rw [hdk]; exact (by decide : ∀ a : HexDir, ¬ SameAxis a (a + 4)) (T.dir c0)
    · rw [hdk, hdk']; exact Or.inl rfl
    · intro x hx
      rw [T.stickOf_head hik, hdk] at hx
      rw [T.stickOf_head hik', hdk']
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨j, hj, ?_⟩
      rw [hfsucc k]
      simp only [walk, nbr]
      abel
  have hsame : ∀ k : ℕ, T.SameStack c0 (walk c0 (T.dir c0 + 4) (k : ℤ)) := by
    intro k
    induction k with
    | zero => simpa using T.sameStack_refl c0
    | succ k ih =>
      have hstep2 : T.SameStack (walk c0 (T.dir c0 + 4) (k : ℤ))
          (walk c0 (T.dir c0 + 4) ((k + 1 : ℕ) : ℤ)) :=
        T.sameStack_of_isStackedPair (hpair k)
      exact SameStack.trans T ih hstep2
  have hinj : Function.Injective fun k : ℕ => T.stickOf (walk c0 (T.dir c0 + 4) (k : ℤ)) := by
    intro k l hkl
    have hkl' : T.stickOf (walk c0 (T.dir c0 + 4) (k : ℤ))
        = T.stickOf (walk c0 (T.dir c0 + 4) (l : ℤ)) := hkl
    have hmem : walk c0 (T.dir c0 + 4) (l : ℤ) ∈ T.stickOf (walk c0 (T.dir c0 + 4) (k : ℤ)) := by
      rw [hkl']; exact T.self_mem_stickOf _
    have hhead := (T.mem_stickOf_iff_head_eq _ _).1 hmem
    have hfk : T.head (walk c0 (T.dir c0 + 4) (k : ℤ)) = walk c0 (T.dir c0 + 4) (k : ℤ) := by
      rw [head, (hstep k).2]; norm_num
    have hfl : T.head (walk c0 (T.dir c0 + 4) (l : ℤ)) = walk c0 (T.dir c0 + 4) (l : ℤ) := by
      rw [head, (hstep l).2]; norm_num
    rw [hfk, hfl] at hhead
    exact_mod_cast (walk_inj c0 (T.dir c0 + 4) hhead).symm
  have hinfinite : (T.Stack c0).Infinite :=
    Set.infinite_of_injective_forall_mem hinj fun k => ⟨_, hsame k, rfl⟩
  exact hinfinite (T.stack_finite hv (by omega) c0)

/-! ### The height of a left-leaning stack -/

/-- Propagation of the ends of the sticks of a left-leaning stack along the stick `w` that they
abut: if one of the cells `nbr r (dir w + 4)`, for `r` on the stick of `w`, is the last cell of
a stick of direction `dir w + 1`, then all of them are. -/
lemma cellOfStick_succ (w : Hex) (k : ℕ) :
    nbr (T.cellOfStick w k) (T.dir w) = T.cellOfStick w (k + 1) := by
  rw [cellOfStick, cellOfStick, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring,
    walk_succ]

/-- A property that propagates in both directions along `{0, …, n-1}` and holds somewhere holds
everywhere. -/
lemma chain_two_sided {P : ℕ → Prop} {m k₀ : ℕ} (hk₀ : k₀ < m) (h : P k₀)
    (hfwd : ∀ k, k + 1 < m → P k → P (k + 1)) (hbwd : ∀ k, k + 1 < m → P (k + 1) → P k) :
    ∀ k < m, P k := by
  have hdown : ∀ j : ℕ, j ≤ k₀ → P (k₀ - j) := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hprev : P (k₀ - j) := ih (by omega)
      refine hbwd (k₀ - (j + 1)) (by omega) ?_
      rw [show k₀ - (j + 1) + 1 = k₀ - j from by omega]
      exact hprev
  have hup : ∀ j : ℕ, k₀ + j < m → P (k₀ + j) := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hprev : P (k₀ + j) := ih (by omega)
      have := hfwd (k₀ + j) (by omega) hprev
      rwa [show k₀ + j + 1 = k₀ + (j + 1) from by omega] at this
  intro k hk
  rcases le_or_gt k k₀ with hle | hlt
  · have := hdown (k₀ - k) (by omega)
    rwa [show k₀ - (k₀ - k) = k from by omega] at this
  · have := hup (k - k₀) (by omega)
    rwa [show k₀ + (k - k₀) = k from by omega] at this

/-- Propagation of the ends of the sticks of a left-leaning stack along the stick `w` that they
abut. -/
lemma corner_chain (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {w : Hex} {k₀ : ℕ} (hk₀ : k₀ < n)
    (h1 : T.dir (nbr (T.cellOfStick w k₀) (T.dir w + 4)) = T.dir w + 1)
    (h2 : T.idx (nbr (T.cellOfStick w k₀) (T.dir w + 4)) = n) :
    ∀ k < n, T.dir (nbr (T.cellOfStick w k) (T.dir w + 4)) = T.dir w + 1 ∧
      T.idx (nbr (T.cellOfStick w k) (T.dir w + 4)) = n := by
  have hnext : ∀ k : ℕ, k + 1 < n →
      nbr (T.cellOfStick w k) (T.dir w + 5) = nbr (T.cellOfStick w (k + 1)) (T.dir w + 4) := by
    intro k _
    rw [← T.cellOfStick_succ w k, nbr_nbr_of_vec (T.cellOfStick w k) (vec_zero_four (T.dir w))]
  refine chain_two_sided hk₀ ⟨h1, h2⟩ ?_ ?_
  · intro k hk hP
    have hd : T.dir (T.cellOfStick w k) = T.dir w := T.cellOfStick_dir w k (by omega)
    have hi : T.idx (T.cellOfStick w k) = k + 1 := T.cellOfStick_idx w k (by omega)
    rw [← hd] at hP ⊢
    have := T.corner_step_forward_A hv hn (p := T.cellOfStick w k) (by omega) hP.1 hP.2
    rw [hd] at this ⊢
    rwa [hnext k hk] at this
  · intro k hk hP
    have hd : T.dir (T.cellOfStick w k) = T.dir w := T.cellOfStick_dir w k (by omega)
    rw [← hnext k hk, ← hd] at hP
    have := T.corner_step_backward_A hv hn (p := T.cellOfStick w k) hP.1 hP.2
    rw [hd] at this
    exact this

/-- The stick lying beyond the far end of a stick of a left-leaning pair points in the direction
`dir s + 5`, so that the ends of the sticks of the stack fill the back corners of that stick. -/
lemma dir_frontCell_of_stackedBy_five (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {s s' : Hex}
    (hst : T.StackedBy s s' (T.dir s + 5)) :
    T.dir (nbr (T.tail s) (T.dir s)) = T.dir s + 5 := by
  have h0n : 0 < n := by omega
  have hdt : T.dir (T.tail s) = T.dir s := T.dir_tail h0n s
  have hit : T.idx (T.tail s) = n := T.idx_tail h0n s
  have hstt : T.StackedBy (T.tail s) s' (T.dir s + 5) :=
    StackedBy.of_mem_stickOf T hst (T.tail_mem_stickOf h0n s)
  have hax := T.sameAxis_dir_nbr_tail_of_stackedBy hv hit hstt
  rw [hdt] at hax
  rcases hax with hw | hw
  · exact hw
  rw [opp_add_five] at hw
  exfalso
  -- the cell `t` at the far end of `s`, and its partner `t'` on the other stick
  have htw : nbr (nbr (T.tail s) (T.dir s)) (T.dir s + 3) = T.tail s :=
    nbr_nbr_cancel (T.tail s) (opp_eq_add_three (T.dir s))
  have hds' : T.dir s' = T.dir s :=
    T.dir_eq_of_leansLeft hv hn ⟨T.dir s + 5, hst, Or.inr rfl⟩
  have hmem' : nbr (T.tail s) (T.dir s + 5) ∈ T.stickOf s' :=
    hst.2.2 _ (T.tail_mem_stickOf h0n s)
  have hdt' : T.dir (nbr (T.tail s) (T.dir s + 5)) = T.dir s := by
    rw [T.dir_of_mem_stickOf hmem', hds']
  by_cases hidx : T.idx (nbr (T.tail s) (T.dir s)) < n
  · have hP := T.not_sameAxis_dir_frontCorner hv hn (p := nbr (T.tail s) (T.dir s)) hidx
    rw [hw, show T.dir s + 2 + 1 = T.dir s + 3 from by
      exact (by decide : ∀ a : HexDir, a + 2 + 1 = a + 3) _, htw, hdt] at hP
    exact hP (sameAxis_add_three (T.dir s))
  · have hidxn : T.idx (nbr (T.tail s) (T.dir s)) = n := by
      have := T.idx_le (nbr (T.tail s) (T.dir s)); omega
    have hopp : (T.dir (nbr (T.tail s) (T.dir s))).opp = T.dir s + 5 := by
      rw [hw, opp_add_two]
    have hdw' : T.dir (nbr (nbr (T.tail s) (T.dir s)) (T.dir s + 5)) = T.dir s + 2 := by
      rw [← hopp, T.pred_dir _ (by omega), hw]
    have hiw' : T.idx (nbr (nbr (T.tail s) (T.dir s)) (T.dir s + 5)) = n - 1 := by
      rw [← hopp, T.pred_idx _ (by omega), hidxn]
    have hcomm : nbr (nbr (T.tail s) (T.dir s)) (T.dir s + 5)
        = nbr (nbr (T.tail s) (T.dir s + 5)) (T.dir s) := nbr_comm _ _ _
    have hP := T.not_sameAxis_dir_frontCorner hv hn
      (p := nbr (nbr (T.tail s) (T.dir s)) (T.dir s + 5)) (by omega)
    rw [hdw', show T.dir s + 2 + 1 = T.dir s + 3 from by
      exact (by decide : ∀ a : HexDir, a + 2 + 1 = a + 3) _, hcomm,
      nbr_nbr_cancel (nbr (T.tail s) (T.dir s + 5))
        (rfl : T.dir s + 3 = (T.dir s).opp), hdt'] at hP
    exact hP (sameAxis_add_three (T.dir s))

/-- **A left-leaning stack has height exactly `n`.** -/
theorem stackHeight_eq_of_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex}
    (h : T.IsLeftLeaningStack c) : T.stackHeight c = n := by
  have h0n : 0 < n := by omega
  obtain ⟨a, b, hsa, hab⟩ := h
  -- normalise the pair so that it is stacked towards `dir + 5`
  obtain ⟨s, s', hs, hst⟩ : ∃ s s', T.SameStack a s ∧ T.StackedBy s s' (T.dir s + 5) := by
    obtain ⟨e, hst, he⟩ := hab
    rcases he with he | he
    · refine ⟨b, a, T.sameStack_of_isStackedPair ⟨e, hst⟩, ?_⟩
      have hdb : T.dir b = T.dir a := T.dir_eq_of_leansLeft hv hn ⟨e, hst, Or.inl he⟩
      have hsym := StackedBy.symm T hst
      rw [he, opp_add_two, ← hdb] at hsym
      exact hsym
    · exact ⟨a, b, T.sameStack_refl a, by rw [← he]; exact hst⟩
  have hstack : T.Stack c = T.Stack s :=
    (T.stack_eq_of_sameStack hsa).trans (T.stack_eq_of_sameStack hs)
  -- the stick `w` beyond the far end of `s`
  have hdt : T.dir (T.tail s) = T.dir s := T.dir_tail h0n s
  have hit : T.idx (T.tail s) = n := T.idx_tail h0n s
  have hdw : T.dir (nbr (T.tail s) (T.dir s)) = T.dir s + 5 :=
    T.dir_frontCell_of_stackedBy_five hv hn hst
  have hw4 : nbr (nbr (T.tail s) (T.dir s)) (T.dir (nbr (T.tail s) (T.dir s)) + 4) = T.tail s := by
    rw [hdw, show T.dir s + 5 + 4 = T.dir s + 3 from by
      exact (by decide : ∀ a : HexDir, a + 5 + 4 = a + 3) _]
    exact nbr_nbr_cancel (T.tail s) (opp_eq_add_three (T.dir s))
  have hposw := T.idx_pos (nbr (T.tail s) (T.dir s))
  have hlew := T.idx_le (nbr (T.tail s) (T.dir s))
  have hcell : T.cellOfStick (nbr (T.tail s) (T.dir s))
      (T.idx (nbr (T.tail s) (T.dir s)) - 1) = nbr (T.tail s) (T.dir s) :=
    T.cellOfStick_idx_sub_one _
  have hchain := T.corner_chain hv hn (w := nbr (T.tail s) (T.dir s))
    (k₀ := T.idx (nbr (T.tail s) (T.dir s)) - 1) (by omega)
    (by rw [hcell, hw4, hdt, hdw]; exact (by decide : ∀ a : HexDir, a = a + 5 + 1) _)
    (by rw [hcell, hw4]; exact hit)
  -- the `n` sticks of the stack
  have hnext : ∀ k : ℕ,
      nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k) (T.dir (nbr (T.tail s) (T.dir s)) + 5)
        = nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) (k + 1))
          (T.dir (nbr (T.tail s) (T.dir s)) + 4) := by
    intro k
    rw [← T.cellOfStick_succ (nbr (T.tail s) (T.dir s)) k,
      nbr_nbr_of_vec (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
        (vec_zero_four (T.dir (nbr (T.tail s) (T.dir s))))]
  have hpairs : ∀ k, k + 1 < n →
      T.IsStackedPair (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
          (T.dir (nbr (T.tail s) (T.dir s)) + 4))
        (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) (k + 1))
          (T.dir (nbr (T.tail s) (T.dir s)) + 4)) := by
    intro k hk
    have hd : T.dir (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
        = T.dir (nbr (T.tail s) (T.dir s)) :=
      T.cellOfStick_dir _ k (by omega)
    have hi : T.idx (T.cellOfStick (nbr (T.tail s) (T.dir s)) k) = k + 1 :=
      T.cellOfStick_idx _ k (by omega)
    have hend : T.EndsAt (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
        (T.dir (T.cellOfStick (nbr (T.tail s) (T.dir s)) k) + 4))
        (T.dir (T.cellOfStick (nbr (T.tail s) (T.dir s)) k) + 1) := by
      rw [hd]; exact Or.inl (hchain k (by omega))
    have hll := T.leansLeft_of_endsAt_corner hv hn
      (p := T.cellOfStick (nbr (T.tail s) (T.dir s)) k) (by omega) hend
    rw [hd, hnext k] at hll
    obtain ⟨e, hste, _⟩ := hll
    exact ⟨e, hste⟩
  -- all these sticks belong to the stack of `s`
  have hbase : T.SameStack s (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s))
      (T.idx (nbr (T.tail s) (T.dir s)) - 1)) (T.dir (nbr (T.tail s) (T.dir s)) + 4)) := by
    rw [hcell, hw4]
    exact T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n s)).symm
  have hsamestack : ∀ k < n, T.SameStack s (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
      (T.dir (nbr (T.tail s) (T.dir s)) + 4)) := by
    refine chain_two_sided (k₀ := T.idx (nbr (T.tail s) (T.dir s)) - 1) (by omega) hbase ?_ ?_
    · intro k hk hP
      exact SameStack.trans T hP (T.sameStack_of_isStackedPair (hpairs k hk))
    · intro k hk hP
      exact SameStack.trans T hP (T.sameStack_of_isStackedPair (hpairs k hk)).symm
  -- the sticks are pairwise distinct
  have hinjOn : Set.InjOn (fun k => T.stickOf (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
      (T.dir (nbr (T.tail s) (T.dir s)) + 4))) ↑(Finset.range n) := by
    intro k hk l hl hkl
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    simp only at hkl
    have hmem : nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) l)
        (T.dir (nbr (T.tail s) (T.dir s)) + 4)
        ∈ T.stickOf (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
          (T.dir (nbr (T.tail s) (T.dir s)) + 4)) := by
      rw [hkl]; exact T.self_mem_stickOf _
    have hhead := (T.mem_stickOf_iff_head_eq _ _).1 hmem
    obtain ⟨hdk, hik⟩ := hchain k hk
    obtain ⟨hdl, hil⟩ := hchain l hl
    have e1 := T.cellOfStick_idx_sub_one (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
      (T.dir (nbr (T.tail s) (T.dir s)) + 4))
    have e2 := T.cellOfStick_idx_sub_one (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) l)
      (T.dir (nbr (T.tail s) (T.dir s)) + 4))
    rw [cellOfStick, hdk, hik] at e1
    rw [cellOfStick, hdl, hil] at e2
    have heq : nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
        (T.dir (nbr (T.tail s) (T.dir s)) + 4)
        = nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) l)
          (T.dir (nbr (T.tail s) (T.dir s)) + 4) := by
      rw [← e1, ← e2, hhead]
    have hcells : T.cellOfStick (nbr (T.tail s) (T.dir s)) k
        = T.cellOfStick (nbr (T.tail s) (T.dir s)) l := by
      simpa [nbr] using heq
    exact T.cellOfStick_injOn _ (by simpa using hk) (by simpa using hl) hcells
  -- counting
  have hcard : ((Finset.range n).image fun k => T.stickOf
      (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
        (T.dir (nbr (T.tail s) (T.dir s)) + 4))).card = n := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]
  have hsub : ↑((Finset.range n).image fun k => T.stickOf
      (nbr (T.cellOfStick (nbr (T.tail s) (T.dir s)) k)
        (T.dir (nbr (T.tail s) (T.dir s)) + 4))) ⊆ T.Stack s := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨_, hsamestack k hk, rfl⟩
  have hle : n ≤ (T.Stack s).ncard := by
    have hmono := Set.ncard_le_ncard hsub (T.stack_finite hv h0n s)
    rwa [Set.ncard_coe_finset, hcard] at hmono
  have hge := T.stack_ncard_le hv h0n s
  rw [stackHeight, hstack]
  omega

end StickTiling

end StickPolyhex
