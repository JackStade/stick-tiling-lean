import Mathlib.Tactic.Conv
import Tiling.Proofs.StackBottom

/-!
# The four neighbours of a left-leaning stack

This file assembles the analysis of the rows above and below a left-leaning stack into the
statement that a left-leaning stack of a valid tiling meets **exactly four** left-leaning
stacks: two on its back side (its top-left and top-right neighbours) and two on its front side
(its bottom-left and bottom-right neighbours).

The first sections set up the bookkeeping of the stack itself: the sticks of a left-leaning
stack are in bijection with the cells of the stick flanking it beyond their far ends, going one
step up the stack corresponds to going one step along that flanking stick, and hence the stack
has exactly one topmost and one bottommost stick.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-! ### Translating a whole stick -/

/-- Translating a walk sideways. -/
lemma walk_nbr_comm (a : Hex) (d g : HexDir) (k : ℤ) :
    walk (nbr a g) d k = nbr (walk a d k) g := by
  simp only [walk, nbr]
  abel

/-- A stick whose head is one step in the direction `g` from the head of a parallel stick is
stacked with it. -/
lemma stackedBy_of_head_nbr {z z' : Hex} {g u : HexDir} (hdz : T.dir z = u) (hdz' : T.dir z' = u)
    (hax : ¬ SameAxis u g) (hh : T.head z' = nbr (T.head z) g) : T.StackedBy z z' g := by
  refine ⟨by rw [hdz]; exact hax, by rw [hdz, hdz']; exact sameAxis_self u, ?_⟩
  intro p hp
  rw [T.mem_stickOf_iff] at hp ⊢
  obtain ⟨k, hk, rfl⟩ := hp
  refine ⟨k, hk, ?_⟩
  rw [cellOfStick, cellOfStick, hdz, hdz', hh, walk_nbr_comm]

/-- Two parallel sticks whose far ends differ by one step in the direction `g` have heads
differing by the same step. -/
lemma head_nbr_of_tail_nbr {z z' : Hex} {g u : HexDir} (hdz : T.dir z = u) (hdz' : T.dir z' = u)
    (ht : T.tail z' = nbr (T.tail z) g) : T.head z' = nbr (T.head z) g := by
  have h1 : T.tail z = walk (T.head z) u ((n - 1 : ℕ) : ℤ) := by rw [tail, cellOfStick, hdz]
  have h2 : T.tail z' = walk (T.head z') u ((n - 1 : ℕ) : ℤ) := by rw [tail, cellOfStick, hdz']
  rw [h1, h2] at ht
  simp only [walk, nbr] at ht ⊢
  linear_combination (norm := module) ht

/-! ### The sticks of a left-leaning stack and the stick flanking it -/

/-- The direction of the stick flanking a left-leaning stack beyond the far ends of its
sticks. -/
lemma dir_flank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) : T.dir (nbr (T.tail c) u) = u + 5 := by
  have h := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl c)).1
  rwa [hu] at h

/-- The cell beyond the far end of any stick of a left-leaning stack lies on the flanking
stick. -/
lemma tail_nbr_mem_flank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c z : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hz : T.SameStack c z) :
    nbr (T.tail z) u ∈ T.stickOf (nbr (T.tail c) u) := by
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz, hu]
  have h := (T.frontCell_mem_of_sameStack hv (by omega) (d := u) (Or.inl hu) hz).2
  rwa [show T.frontCell u z = nbr (T.tail z) u from by rw [frontCell, endCell, if_pos hdz],
    show T.frontCell u c = nbr (T.tail c) u from by rw [frontCell, endCell, if_pos hu]] at h

/-- A cell of a stick whose index is `n` is the far end of that stick. -/
lemma eq_tail_of_mem_of_idx_eq (hn : 0 < n) {v w : Hex} (hw : w ∈ T.stickOf v)
    (hi : T.idx w = n) : w = T.tail v := by
  rw [T.mem_stickOf_iff] at hw
  obtain ⟨k, hk, rfl⟩ := hw
  rw [T.cellOfStick_idx v k hk] at hi
  rw [tail, show n - 1 = k from by omega]

/-- A cell of a stick whose index is `1` is the near end of that stick. -/
lemma eq_head_of_mem_of_idx_eq {v w : Hex} (hw : w ∈ T.stickOf v)
    (hi : T.idx w = 1) : w = T.head v := by
  rw [T.mem_stickOf_iff] at hw
  obtain ⟨k, hk, rfl⟩ := hw
  rw [T.cellOfStick_idx v k hk] at hi
  rw [cellOfStick, show k = 0 from by omega]
  simp [walk]

/-- **A stick of a left-leaning stack whose far end is not the far end of the flanking stick has
a stick of the stack directly above it.** -/
lemma exists_stackedBy_up' (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c z : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hz : T.SameStack c z)
    (hi : T.idx (nbr (T.tail z) u) ≠ n) :
    ∃ z', T.SameStack c z' ∧ T.StackedBy z z' (u + 5) := by
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz, hu]
  have hmem := T.tail_nbr_mem_flank hv hn hL hu hz
  have hdF : T.dir (nbr (T.tail z) u) = u + 5 := by
    rw [T.dir_of_mem_stickOf hmem]
    exact T.dir_flank hv hn hL hu
  have hstep : nbr (nbr (T.tail z) u) (u + 5) ∈ T.stickOf (nbr (T.tail c) u) := by
    have h := T.nbr_dir_mem_stickOf (nbr (T.tail z) u) (lt_of_le_of_ne (T.idx_le _) hi)
    rw [hdF, T.stickOf_eq_of_mem hmem] at h
    exact h
  obtain ⟨z', hz', hz'eq⟩ := T.exists_sameStack_of_mem_flankingStick hv hn hL
    (by rw [hu]; exact hstep)
  rw [hu] at hz'eq
  have hdz' : T.dir z' = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz', hu]
  refine ⟨z', hz', T.stackedBy_of_head_nbr hdz hdz'
    ((by decide : ∀ a : HexDir, ¬ SameAxis a (a + 5)) u) ?_⟩
  refine T.head_nbr_of_tail_nbr hdz hdz' ?_
  have : nbr (T.tail z') u = nbr (nbr (T.tail z) (u + 5)) u := by
    rw [hz'eq, nbr_comm]
  simp only [nbr] at this ⊢
  linear_combination (norm := module) this

/-- **A stick of a left-leaning stack whose far end is not the near end of the flanking stick has
a stick of the stack directly below it.** -/
lemma exists_stackedBy_down' (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c z : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hz : T.SameStack c z)
    (hi : T.idx (nbr (T.tail z) u) ≠ 1) :
    ∃ z', T.SameStack c z' ∧ T.StackedBy z z' (u + 2) := by
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz, hu]
  have hmem := T.tail_nbr_mem_flank hv hn hL hu hz
  have hdF : T.dir (nbr (T.tail z) u) = u + 5 := by
    rw [T.dir_of_mem_stickOf hmem]
    exact T.dir_flank hv hn hL hu
  have hstep : nbr (nbr (T.tail z) u) (u + 2) ∈ T.stickOf (nbr (T.tail c) u) := by
    have h := T.nbr_dir_opp_mem_stickOf (nbr (T.tail z) u)
      (lt_of_le_of_ne (T.idx_pos _) (Ne.symm hi))
    rw [hdF, opp_add_five, T.stickOf_eq_of_mem hmem] at h
    exact h
  obtain ⟨z', hz', hz'eq⟩ := T.exists_sameStack_of_mem_flankingStick hv hn hL
    (by rw [hu]; exact hstep)
  rw [hu] at hz'eq
  have hdz' : T.dir z' = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz', hu]
  refine ⟨z', hz', T.stackedBy_of_head_nbr hdz hdz'
    ((by decide : ∀ a : HexDir, ¬ SameAxis a (a + 2)) u) ?_⟩
  refine T.head_nbr_of_tail_nbr hdz hdz' ?_
  have : nbr (T.tail z') u = nbr (nbr (T.tail z) (u + 2)) u := by
    rw [hz'eq, nbr_comm]
  simp only [nbr] at this ⊢
  linear_combination (norm := module) this

/-- **A stick of a left-leaning stack which is not the topmost one has a stick of the stack
directly above it.** -/
lemma exists_stackedBy_up (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x z : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (htop : nbr (T.tail x) u = T.tail (nbr (T.tail c) u)) (hz : T.SameStack c z) :
    T.stickOf z = T.stickOf x ∨ ∃ z', T.SameStack c z' ∧ T.StackedBy z z' (u + 5) := by
  have h0n : 0 < n := by omega
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz, hu]
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx, hu]
  by_cases hi : T.idx (nbr (T.tail z) u) = n
  · left
    have heq : nbr (T.tail z) u = nbr (T.tail x) u := by
      rw [htop]
      exact T.eq_tail_of_mem_of_idx_eq h0n (T.tail_nbr_mem_flank hv hn hL hu hz) hi
    refine T.stickOf_eq_of_frontCell_eq h0n (d := u) ?_
    rw [show T.frontCell u z = nbr (T.tail z) u from by rw [frontCell, endCell, if_pos hdz],
      show T.frontCell u x = nbr (T.tail x) u from by rw [frontCell, endCell, if_pos hdx]]
    exact heq
  · exact Or.inr (T.exists_stackedBy_up' hv hn hL hu hz hi)

/-- **A stick of a left-leaning stack which is not the bottommost one has a stick of the stack
directly below it.** -/
lemma exists_stackedBy_down (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c y z : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hy : T.SameStack c y)
    (hbot : nbr (T.tail y) u = T.head (nbr (T.tail c) u)) (hz : T.SameStack c z) :
    T.stickOf z = T.stickOf y ∨ ∃ z', T.SameStack c z' ∧ T.StackedBy z z' (u + 2) := by
  have h0n : 0 < n := by omega
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz, hu]
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hy, hu]
  by_cases hi : T.idx (nbr (T.tail z) u) = 1
  · left
    have heq : nbr (T.tail z) u = nbr (T.tail y) u := by
      rw [hbot]
      exact T.eq_head_of_mem_of_idx_eq (T.tail_nbr_mem_flank hv hn hL hu hz) hi
    refine T.stickOf_eq_of_frontCell_eq h0n (d := u) ?_
    rw [show T.frontCell u z = nbr (T.tail z) u from by rw [frontCell, endCell, if_pos hdz],
      show T.frontCell u y = nbr (T.tail y) u from by rw [frontCell, endCell, if_pos hdy]]
    exact heq
  · exact Or.inr (T.exists_stackedBy_down' hv hn hL hu hz hi)

/-- **Every left-leaning stack has a topmost stick**: a stick whose far end sits at the very end
of the stick flanking the stack. -/
lemma exists_topStick (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ x, T.SameStack c x ∧ nbr (T.tail x) u = T.tail (nbr (T.tail c) u) := by
  obtain ⟨x, hx, hxeq⟩ := T.exists_sameStack_of_mem_flankingStick hv hn hL
    (y := T.tail (nbr (T.tail c) u)) (by rw [hu]; exact T.tail_mem_stickOf (by omega) _)
  rw [hu] at hxeq
  exact ⟨x, hx, hxeq⟩

/-- **Every left-leaning stack has a bottommost stick.** -/
lemma exists_botStick (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) :
    ∃ y, T.SameStack c y ∧ nbr (T.tail y) u = T.head (nbr (T.tail c) u) := by
  obtain ⟨y, hy, hyeq⟩ := T.exists_sameStack_of_mem_flankingStick hv hn hL
    (y := T.head (nbr (T.tail c) u)) (by rw [hu]; exact T.head_mem_stickOf _)
  rw [hu] at hyeq
  exact ⟨y, hy, hyeq⟩


/-! ### Classification of the cells adjacent to a left-leaning stack -/

/-- The two sticks of a stacked pair of parallel sticks have their ends one step apart. -/
lemma head_tail_nbr_of_stackedBy {z z' : Hex} {g u : HexDir} (hn : 0 < n)
    (hst : T.StackedBy z z' g) (hdz : T.dir z = u) (hdz' : T.dir z' = u) :
    T.head z' = nbr (T.head z) g ∧ T.tail z' = nbr (T.tail z) g := by
  have hdt : T.dir (T.tail z) = u := by rw [T.dir_tail hn z, hdz]
  have hit : T.idx (T.tail z) = n := T.idx_tail hn z
  have hend := T.endsAt_nbr_of_stackedBy_tail (StackedBy.of_mem_stickOf T hst
    (T.tail_mem_stickOf hn z)) hit
  have hmem : nbr (T.tail z) g ∈ T.stickOf z' := hst.2.2 (T.tail z) (T.tail_mem_stickOf hn z)
  have hidx : T.idx (nbr (T.tail z) g) = n := by
    rcases hend with ⟨-, hi⟩ | ⟨hd, -⟩
    · exact hi
    · exfalso
      rw [T.dir_of_mem_stickOf hmem, hdz', hdt] at hd
      exact (by decide : ∀ a : HexDir, a ≠ a.opp) u hd
  have htail : T.tail z' = nbr (T.tail z) g := (T.eq_tail_of_mem_of_idx_eq hn hmem hidx).symm
  exact ⟨T.head_nbr_of_tail_nbr hdz hdz' htail, htail⟩

/-- The cell beyond the near end of any stick of a left-leaning stack lies on the stick flanking
the stack on its front side. -/
lemma head_nbr_mem_flank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c z : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hz : T.SameStack c z) :
    nbr (T.head z) (u + 3) ∈ T.stickOf (nbr (T.head c) (u + 3)) := by
  have hne3 : u ≠ u + 3 := (by decide : ∀ a : HexDir, a ≠ a + 3) u
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz, hu]
  have hax : SameAxis (u + 3) (T.dir c) := Or.inr (by rw [hu, opp_add_three])
  have h := (T.frontCell_mem_of_sameStack hv (by omega) (d := u + 3) hax hz).2
  rwa [show T.frontCell (u + 3) z = nbr (T.head z) (u + 3) from by
      rw [frontCell, endCell, if_neg (by rw [hdz]; exact hne3)],
    show T.frontCell (u + 3) c = nbr (T.head c) (u + 3) from by
      rw [frontCell, endCell, if_neg (by rw [hu]; exact hne3)]] at h

/-- The cell just above a cell of a left-leaning stack is either again a cell of the stack, or a
cell of the row above the topmost stick. -/
lemma up_classification (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x p : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (htop : nbr (T.tail x) u = T.tail (nbr (T.tail c) u)) (hp : T.SameStack c p) :
    T.SameStack c (nbr p (u + 5)) ∨ ∃ j, j < n ∧ nbr p (u + 5) = T.upCell u x j := by
  have hdp : T.dir p = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hp, hu]
  have hpos := T.idx_pos p
  have hle := T.idx_le p
  rcases T.exists_stackedBy_up hv hn hL hu hx htop hp with hst | ⟨z', hz', hstk⟩
  · right
    have hhead : T.head p = T.head x :=
      (T.mem_stickOf_iff_head_eq x p).1 (by rw [← hst]; exact T.self_mem_stickOf p)
    refine ⟨T.idx p - 1, by omega, ?_⟩
    rw [upCell, ← hhead, ← hdp, ← cellOfStick, T.cellOfStick_idx_sub_one p]
  · left
    have hmem : nbr p (u + 5) ∈ T.stickOf z' := hstk.2.2 p (T.self_mem_stickOf p)
    exact SameStack.trans T hz' (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem hmem).symm)

/-- The cell just below a cell of a left-leaning stack is either again a cell of the stack, or a
cell of the row below the bottommost stick. -/
lemma down_classification (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c y p : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hy : T.SameStack c y)
    (hbot : nbr (T.tail y) u = T.head (nbr (T.tail c) u)) (hp : T.SameStack c p) :
    T.SameStack c (nbr p (u + 2)) ∨ ∃ j, j < n ∧ nbr p (u + 2) = T.downCell u y j := by
  have hdp : T.dir p = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hp, hu]
  have hpos := T.idx_pos p
  have hle := T.idx_le p
  rcases T.exists_stackedBy_down hv hn hL hu hy hbot hp with hst | ⟨z', hz', hstk⟩
  · right
    have hhead : T.head p = T.head y :=
      (T.mem_stickOf_iff_head_eq y p).1 (by rw [← hst]; exact T.self_mem_stickOf p)
    refine ⟨T.idx p - 1, by omega, ?_⟩
    rw [downCell, ← hhead, ← hdp, ← cellOfStick, T.cellOfStick_idx_sub_one p]
  · left
    have hmem : nbr p (u + 2) ∈ T.stickOf z' := hstk.2.2 p (T.self_mem_stickOf p)
    exact SameStack.trans T hz' (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem hmem).symm)

/-! ### Comparing two stacks through the cells beyond the far ends of their sticks -/

/-- Two cells of one stick differ by at most `n - 1` steps along the stick. -/
lemma exists_walk_of_mem_stickOf_abs_lt {z p q : Hex} (hp : p ∈ T.stickOf z)
    (hq : q ∈ T.stickOf z) : ∃ k : ℤ, |k| < (n : ℤ) ∧ p = walk q (T.dir z) k := by
  rw [T.mem_stickOf_iff] at hp hq
  obtain ⟨kp, hkp, rfl⟩ := hp
  obtain ⟨kq, hkq, rfl⟩ := hq
  refine ⟨(kp : ℤ) - kq, by rw [abs_lt]; omega, ?_⟩
  simp only [cellOfStick, walk_walk]
  congr 1
  omega

/-- The cell just beyond the far end of a stick of direction `u`. -/
lemma frontCell_eq_walk (hn : 0 < n) {z : Hex} {u : HexDir} (hdz : T.dir z = u) :
    T.frontCell u z = walk z u ((n : ℤ) - T.idx z + 1) := by
  rw [frontCell, endCell, if_pos hdz, T.tail_eq_walk hn, hdz, nbr_eq_walk_one, walk_walk]

/-- The stick flanking a left-leaning stack beyond the far ends of its sticks slants left. -/
lemma dir_frontCell_of_isLeftLeaningStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) : T.dir (T.frontCell u c) = u + 5 := by
  rw [frontCell, endCell, if_pos hu]
  exact T.dir_flank hv hn hL hu

/-- **Distinguishing two stacks.**  If the cells beyond the far ends of two horizontal sticks
differ by a nonzero multiple of the direction of the sticks, or by more than `n - 1` steps
across, then the two sticks belong to different stacks. -/
lemma not_sameStack_of_frontCell_add (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {p q : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack p) (hu : T.dir p = u) {a b : ℤ}
    (hpq : T.frontCell u q = T.frontCell u p + a • u.vec + b • (u + 5).vec)
    (hab : a ≠ 0 ∨ (n : ℤ) ≤ |b|) : ¬ T.SameStack p q := by
  intro hs
  have hmem := (T.frontCell_mem_of_sameStack hv (by omega) (d := u) (Or.inl hu) hs).2
  obtain ⟨k, hk, hkeq⟩ := T.exists_walk_of_mem_stickOf_abs_lt hmem (T.self_mem_stickOf _)
  rw [T.dir_frontCell_of_isLeftLeaningStack hv hn hL hu] at hkeq
  have key : a • u.vec = (k - b) • (u + 5).vec := by
    rw [hkeq] at hpq
    simp only [walk] at hpq
    rw [sub_smul]
    linear_combination (norm := module) -hpq
  obtain ⟨ha, hkb⟩ := smul_vec_eq_smul_vec ((by decide : ∀ a : HexDir, a ≠ a + 5) u)
    (by rw [opp_add_five]; exact (by decide : ∀ a : HexDir, a ≠ a + 2) u) key
  have hbk : b = k := by omega
  rcases hab with h | h
  · exact h ha
  · rw [hbk] at h; omega

/-! ### The topmost and the bottommost stick, and the two flanking sticks -/

/-- Being a left-leaning stack is a property of the stack. -/
lemma isLeftLeaningStack_of_sameStack {c z : Hex} (hL : T.IsLeftLeaningStack c)
    (hz : T.SameStack c z) : T.IsLeftLeaningStack z := by
  obtain ⟨a, b, hca, hab⟩ := hL
  exact ⟨a, b, SameStack.trans T (SameStack.symm T hz) hca, hab⟩

/-- Two parallel sticks whose far ends have the same neighbour have the same near end. -/
lemma eq_head_of_tail_nbr_eq {z x : Hex} {u : HexDir} (hdz : T.dir z = u)
    (hdx : T.dir x = u) (h : nbr (T.tail z) u = nbr (T.tail x) u) : T.head z = T.head x := by
  simp only [tail, cellOfStick, hdz, hdx, walk, nbr] at h
  linear_combination (norm := module) h

/-- **The stick of a left-leaning stack whose back corner beyond the far end lies outside the
stack is the topmost stick**: its far end sits at the very end of the flanking stick. -/
lemma tail_nbr_eq_tail_flank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (hne : ¬ T.SameStack c (nbr (T.tail x) (u + 5))) :
    nbr (T.tail x) u = T.tail (nbr (T.tail c) u) := by
  have h0n : 0 < n := by omega
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx, hu]
  by_cases hi : T.idx (nbr (T.tail x) u) = n
  · exact T.eq_tail_of_mem_of_idx_eq h0n (T.tail_nbr_mem_flank hv hn hL hu hx) hi
  · exfalso
    obtain ⟨z', hz', hstk⟩ := T.exists_stackedBy_up' hv hn hL hu hx hi
    have hdz' : T.dir z' = u := by
      rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz', hu]
    have htail := (T.head_tail_nbr_of_stackedBy h0n hstk hdx hdz').2
    refine hne (SameStack.trans T hz' (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem ?_).symm))
    rw [← htail]
    exact T.tail_mem_stickOf h0n z'

/-- **The stick of a left-leaning stack whose front corner beyond the near end lies outside the
stack is the bottommost stick.** -/
lemma tail_nbr_eq_head_flank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c y : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hy : T.SameStack c y)
    (hne : ¬ T.SameStack c (nbr (T.head y) (u + 2))) :
    nbr (T.tail y) u = T.head (nbr (T.tail c) u) := by
  have h0n : 0 < n := by omega
  have hdy : T.dir y = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hy, hu]
  by_cases hi : T.idx (nbr (T.tail y) u) = 1
  · exact T.eq_head_of_mem_of_idx_eq (T.tail_nbr_mem_flank hv hn hL hu hy) hi
  · exfalso
    obtain ⟨z', hz', hstk⟩ := T.exists_stackedBy_down' hv hn hL hu hy hi
    have hdz' : T.dir z' = u := by
      rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz', hu]
    have hhead := (T.head_tail_nbr_of_stackedBy h0n hstk hdy hdz').1
    refine hne (SameStack.trans T hz' (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem ?_).symm))
    rw [← hhead]
    exact T.head_mem_stickOf z'

/-! ### Sticks that do not belong to a left-leaning stack -/

/-- The cell just beyond the far end of a stick of a left-leaning stack, seen from the last cell
of that stick. -/
lemma dir_nbr_of_isLeftLeaningStack_idx_eq_n (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {z : Hex}
    (hL : T.IsLeftLeaningStack z) (hi : T.idx z = n) :
    T.dir (nbr z (T.dir z)) = T.dir z + 5 := by
  have hz : T.tail z = z := by
    rw [tail, show n - 1 = T.idx z - 1 from by omega, T.cellOfStick_idx_sub_one]
  have h := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl z)).1
  rwa [hz] at h

/-- The cell just beyond the near end of a stick of a left-leaning stack, seen from the first
cell of that stick. -/
lemma dir_nbr_of_isLeftLeaningStack_idx_eq_one (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {z : Hex}
    (hL : T.IsLeftLeaningStack z) (hi : T.idx z = 1) :
    T.dir (nbr z (T.dir z + 3)) = T.dir z + 2 := by
  have hz : T.head z = z := by rw [head, hi]; simp
  have h := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl z)).2
  rwa [hz, opp_eq_add_three] at h

/-- **A left-slanting stick ending against a horizontal stick lying just below it does not
belong to a left-leaning stack.** -/
lemma not_isLeftLeaningStack_slantEndAbove (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {z : Hex} {u : HexDir}
    (hs : T.SlantEndAbove u z) (hbelow : T.dir (nbr z (u + 2)) = u) :
    ¬ T.IsLeftLeaningStack z := by
  intro hL
  rcases hs with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · have h := T.dir_nbr_of_isLeftLeaningStack_idx_eq_n hv hn hL hi
    rw [hd, hbelow] at h
    exact (by decide : ∀ a : HexDir, ¬ (a = a + 2 + 5)) u h
  · have h := T.dir_nbr_of_isLeftLeaningStack_idx_eq_one hv hn hL hi
    rw [hd, (by decide : ∀ a : HexDir, a + 5 + 3 = a + 2), hbelow] at h
    exact (by decide : ∀ a : HexDir, ¬ (a = a + 5 + 2)) u h

/-- **A left-slanting stick ending against a horizontal stick lying just above it does not
belong to a left-leaning stack.** -/
lemma not_isLeftLeaningStack_slantEndBelow (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {z : Hex} {u : HexDir}
    (hs : T.SlantEndBelow u z) (habove : T.dir (nbr z (u + 5)) = u) :
    ¬ T.IsLeftLeaningStack z := by
  intro hL
  rcases hs with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · have h := T.dir_nbr_of_isLeftLeaningStack_idx_eq_one hv hn hL hi
    rw [hd, (by decide : ∀ a : HexDir, a + 2 + 3 = a + 5), habove] at h
    exact (by decide : ∀ a : HexDir, ¬ (a = a + 2 + 2)) u h
  · have h := T.dir_nbr_of_isLeftLeaningStack_idx_eq_n hv hn hL hi
    rw [hd, habove] at h
    exact (by decide : ∀ a : HexDir, ¬ (a = a + 5 + 5)) u h

/-- **The stick flanking a left-leaning stack beyond the far ends of its sticks does not itself
belong to a left-leaning stack.**  Its own far end lies beside the horizontal stick filling the
space `A` above the topmost stick of the stack. -/
lemma not_isLeftLeaningStack_flank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (htop : nbr (T.tail x) u = T.tail (nbr (T.tail c) u))
    (hin : T.idx (nbr (T.tail x) (u + 5)) < n) :
    ¬ T.IsLeftLeaningStack (nbr (T.tail c) u) := by
  intro hLF
  have h0n : 0 < n := by omega
  set F := nbr (T.tail c) u with hF
  have hdF : T.dir F = u + 5 := T.dir_flank hv hn hL hu
  have hLt : T.IsLeftLeaningStack (T.tail F) := T.isLeftLeaningStack_of_sameStack hLF
    (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.tail_mem_stickOf h0n F)).symm)
  have hdt : T.dir (T.tail F) = u + 5 := by rw [T.dir_tail h0n, hdF]
  have h := T.dir_nbr_of_isLeftLeaningStack_idx_eq_n hv hn hLt (T.idx_tail h0n F)
  rw [hdt, show nbr (T.tail F) (u + 5) = nbr (nbr (T.tail x) (u + 5)) u from by
    rw [← htop, nbr_comm]] at h
  have hdA : T.dir (nbr (T.tail x) (u + 5)) = u := (T.dir_backCorner_beyond_tail hv hn hL hu hx).1
  have hmem := T.nbr_dir_mem_stickOf (nbr (T.tail x) (u + 5)) hin
  rw [hdA] at hmem
  rw [T.dir_of_mem_stickOf hmem, hdA] at h
  exact (by decide : ∀ a : HexDir, ¬ (a = a + 5 + 5)) u h

/-- **The stick flanking a left-leaning stack beyond the near ends of its sticks does not itself
belong to a left-leaning stack.**  Its own near end lies beside the horizontal stick filling the
space `B` above the near end of the topmost stick of the stack. -/
lemma not_isLeftLeaningStack_frontFlank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x : Hex} {u : HexDir}
    {s : ℕ} (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hx : T.SameStack c x)
    (htop : nbr (T.tail x) u = T.tail (nbr (T.tail c) u))
    (hds : T.dir (T.upCell u x s) = u) (his : T.idx (T.upCell u x s) = n) (hsn : s + 2 ≤ n) :
    ¬ T.IsLeftLeaningStack (nbr (T.head c) (u + 3)) := by
  intro hLE
  have h0n : 0 < n := by omega
  have hne3 : u ≠ u + 3 := (by decide : ∀ a : HexDir, a ≠ a + 3) u
  have hdx : T.dir x = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hx, hu]
  set E := nbr (T.head c) (u + 3) with hE
  have hdE : T.dir E = u + 2 := by
    have h2 := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl c)).2
    rwa [hu, opp_eq_add_three] at h2
  have hfc : T.frontCell (u + 3) c = E := by
    rw [frontCell, endCell, if_neg (by rw [hu]; exact hne3)]
  have hax : SameAxis (u + 3) (T.dir c) := Or.inr (by rw [hu, opp_add_three])
  obtain ⟨z, hz, hzeq⟩ := T.exists_sameStack_frontCell_eq hv hn hL hax
    (y := T.head E) (by rw [hfc]; exact T.head_mem_stickOf E)
  have hdz : T.dir z = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz, hu]
  have hzE : nbr (T.head z) (u + 3) = T.head E := by
    rwa [frontCell, endCell, if_neg (by rw [hdz]; exact hne3)] at hzeq
  -- the stick `z` beside the near end of the flanking stick is the topmost stick of the stack
  have hztop : nbr (T.tail z) u = T.tail (nbr (T.tail c) u) := by
    by_cases hi : T.idx (nbr (T.tail z) u) = n
    · exact T.eq_tail_of_mem_of_idx_eq h0n (T.tail_nbr_mem_flank hv hn hL hu hz) hi
    · exfalso
      obtain ⟨z', hz', hstk⟩ := T.exists_stackedBy_up' hv hn hL hu hz hi
      have hdz' : T.dir z' = u := by
        rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz', hu]
      have hhead := (T.head_tail_nbr_of_stackedBy h0n hstk hdz hdz').1
      have hmem := T.head_nbr_mem_flank hv hn hL hu hz'
      rw [show nbr (T.head z') (u + 3) = nbr (T.head E) (u + 5) from by
        rw [hhead, ← hzE, nbr_comm]] at hmem
      have hnot := T.nbr_dir_opp_not_mem_stickOf (c := T.head E) (T.idx_head E)
      rw [T.dir_head E, hdE, opp_add_two, T.stickOf_eq_of_mem (T.head_mem_stickOf E)] at hnot
      exact hnot hmem
  have hheads : T.head z = T.head x :=
    T.eq_head_of_tail_nbr_eq hdz hdx (hztop.trans htop.symm)
  have hEx : T.head E = nbr (T.head x) (u + 3) := by rw [← hzE, hheads]
  have hLh : T.IsLeftLeaningStack (T.head E) := T.isLeftLeaningStack_of_sameStack hLE
    (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem (T.head_mem_stickOf E)).symm)
  have h := T.dir_nbr_of_isLeftLeaningStack_idx_eq_one hv hn hLh (T.idx_head E)
  rw [T.dir_head E, hdE, (by decide : ∀ a : HexDir, a + 2 + 3 = a + 5), hEx,
    nbr_nbr_of_vec (T.head x) (vec_three_five u)] at h
  rw [T.dir_of_mem_stickOf (T.backCorner_head_mem_stickOf hds his hsn), hds] at h
  exact (by decide : ∀ a : HexDir, ¬ (a = a + 2 + 2)) u h

/-! ### All the cells adjacent to a left-leaning stack -/

/-- The cell just beyond a cell of a left-leaning stack, in the direction of its sticks, is
either again a cell of the stack or a cell of the stick flanking the far ends. -/
lemma nbr_dir_classification (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c p : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hp : T.SameStack c p) :
    T.SameStack c (nbr p u) ∨ nbr p u ∈ T.stickOf (nbr (T.tail c) u) := by
  have hdp : T.dir p = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hp, hu]
  by_cases hi : T.idx p = n
  · refine Or.inr ?_
    have hpt : T.tail p = p := by
      rw [tail, show n - 1 = T.idx p - 1 from by omega, T.cellOfStick_idx_sub_one]
    have h := T.tail_nbr_mem_flank hv hn hL hu hp
    rwa [hpt] at h
  · refine Or.inl ?_
    have hmem := T.nbr_dir_mem_stickOf p (lt_of_le_of_ne (T.idx_le p) hi)
    rw [hdp] at hmem
    exact SameStack.trans T hp (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem hmem).symm)

/-- The cell just beyond a cell of a left-leaning stack, against the direction of its sticks, is
either again a cell of the stack or a cell of the stick flanking the near ends. -/
lemma nbr_opp_dir_classification (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c p : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hp : T.SameStack c p) :
    T.SameStack c (nbr p (u + 3)) ∨ nbr p (u + 3) ∈ T.stickOf (nbr (T.head c) (u + 3)) := by
  have hdp : T.dir p = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hp, hu]
  by_cases hi : T.idx p = 1
  · refine Or.inr ?_
    have hph : T.head p = p := by rw [head, hi]; simp
    have h := T.head_nbr_mem_flank hv hn hL hu hp
    rwa [hph] at h
  · refine Or.inl ?_
    have hmem := T.nbr_dir_opp_mem_stickOf p (lt_of_le_of_ne (T.idx_pos p) (Ne.symm hi))
    rw [hdp, opp_eq_add_three] at hmem
    exact SameStack.trans T hp (T.sameStack_of_stickOf_eq (T.stickOf_eq_of_mem hmem).symm)

/-- **All the cells adjacent to a left-leaning stack.**  Let `x` be the topmost and `y` the
bottommost stick of a left-leaning stack of direction `u`.  Every neighbour of a cell of the
stack is either again a cell of the stack, or a cell of one of the two sticks flanking the
stack, or a cell of the row just above `x` (together with the corner cell diagonally above the
near end of `x`), or a cell of the row just below `y`. -/
theorem nbr_classification (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c x y p : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u)
    (hx : T.SameStack c x) (htop : nbr (T.tail x) u = T.tail (nbr (T.tail c) u))
    (hy : T.SameStack c y) (hbot : nbr (T.tail y) u = T.head (nbr (T.tail c) u))
    (hp : T.SameStack c p) (e : HexDir) :
    T.SameStack c (nbr p e) ∨
      nbr p e ∈ T.stickOf (nbr (T.tail c) u) ∨
      nbr p e ∈ T.stickOf (nbr (T.head c) (u + 3)) ∨
      (∃ j, j < n ∧ nbr p e = T.upCell u x j) ∨
      nbr p e = nbr (T.head x) (u + 4) ∨
      (∃ j, j ≤ n ∧ nbr p e = T.downCell u y j) := by
  rcases hexDir_cases u e with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases T.nbr_dir_classification hv hn hL hu hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · -- the direction `u + 1`, reached through the cell below
    rw [← nbr_nbr_of_vec p ((by decide : ∀ a : HexDir, (a + 2).vec + a.vec = (a + 1).vec) u)]
    rcases T.down_classification hv hn hL hu hy hbot hp with h | ⟨j, hj, hjeq⟩
    · rcases T.nbr_dir_classification hv hn hL hu h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j + 1, by omega, ?_⟩))))
      rw [hjeq, T.downCell_succ]
  · rcases T.down_classification hv hn hL hu hy hbot hp with h | ⟨j, hj, hjeq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by omega, hjeq⟩))))
  · rcases T.nbr_opp_dir_classification hv hn hL hu hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · -- the direction `u + 4`, reached through the cell above
    rw [← nbr_nbr_of_vec p (vec_five_three u)]
    rcases T.up_classification hv hn hL hu hx htop hp with h | ⟨j, hj, hjeq⟩
    · rcases T.nbr_opp_dir_classification hv hn hL hu h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
    · rw [hjeq]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [T.upCell_zero]
        exact nbr_nbr_of_vec (T.head x) (vec_five_three u)
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j - 1, by omega, ?_⟩)))
        conv_lhs => rw [show j = (j - 1) + 1 from by omega]
        exact T.upCell_pred u x (j - 1)
  · rcases T.up_classification hv hn hL hu hx htop hp with h | ⟨j, hj, hjeq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, hjeq⟩)))

end StickTiling

end StickPolyhex
