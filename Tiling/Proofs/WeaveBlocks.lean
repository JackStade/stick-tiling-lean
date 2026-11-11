import Tiling.Proofs.WeaveShear

/-!
# The blocks of a weave-pattern tiling

A *block* of a weave-pattern tiling is a left-leaning stack of horizontal sticks, together with
the two left-slanting sticks flanking it.  This file records how a block is built up from its
bottom stick: the *back flank* `StickTiling.flank u c`, the cell just beyond the far end of the
stick through `c`, lies on the left-slanting stick flanking the stack from behind, and its index
counts the sticks of the stack from the bottom.

The main results are the two stepping lemmas `StickTiling.block_up` and
`StickTiling.block_down`: as long as the flank cell is not the last (resp. the first) cell of the
flanking stick, the cell directly above (resp. below) a horizontal cell is again a horizontal
cell of the same stack with the same index, and the index of its flank cell is one larger
(resp. smaller).  Together with `StickTiling.flank_idx_eq_one_of_top` they say that the flank
index of a horizontal cell measures its height inside its block.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- The cell just beyond the far end of the stick through `c`, in the direction `u`.  For a
horizontal cell of a weave-pattern tiling this is the cell of the left-slanting stick flanking
its block from behind. -/
def flank (u : HexDir) (c : Hex) : Hex := nbr (T.tail c) u

lemma flank_def (u : HexDir) (c : Hex) : T.flank u c = nbr (T.tail c) u := rfl

/-- The flank cell only depends on the stick. -/
lemma flank_congr {u : HexDir} {c c' : Hex} (h : T.stickOf c = T.stickOf c') :
    T.flank u c = T.flank u c' := by
  have : T.head c = T.head c' := by
    have hmem : c ∈ T.stickOf c' := by rw [← h]; exact T.self_mem_stickOf c
    exact (T.mem_stickOf_iff_head_eq c' c).1 hmem
  rw [flank, flank, tail, tail, cellOfStick, cellOfStick, this]
  congr 2
  have h1 : T.dir (T.head c) = T.dir c := T.dir_head c
  have h2 : T.dir (T.head c') = T.dir c' := T.dir_head c'
  rw [← h1, ← h2, this]

lemma flank_mem_of_sameStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c z : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hz : T.SameStack c z) :
    T.flank u z ∈ T.stickOf (T.flank u c) :=
  T.tail_nbr_mem_flank hv hn hL hu hz

/-- The direction of the stick flanking a left-leaning stack from behind. -/
lemma dir_flank_eq (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) : T.dir (T.flank u c) = u + 5 :=
  T.dir_flank hv hn hL hu

/-- **Climbing a block.**  If the flank cell of a horizontal cell `c` is not the last cell of the
flanking stick, then the cell directly above `c` lies on the next stick of the block: it is again
horizontal with the same index, and its flank cell is the next cell of the flanking stick. -/
theorem block_up (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hlt : T.idx (T.flank u c) < n) :
    T.dir (nbr c (u + 5)) = u ∧ T.idx (nbr c (u + 5)) = T.idx c ∧
      T.SameStack c (nbr c (u + 5)) ∧
      T.flank u (nbr c (u + 5)) = nbr (T.flank u c) (u + 5) ∧
      T.idx (T.flank u (nbr c (u + 5))) = T.idx (T.flank u c) + 1 := by
  have h0n : 0 < n := by omega
  obtain ⟨z', hz', hst⟩ := T.exists_stackedBy_up' hv hn hL hu (T.sameStack_refl c)
    (by simpa [flank] using Nat.ne_of_lt hlt)
  have hdz' : T.dir z' = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz', hu]
  have hmem : nbr c (u + 5) ∈ T.stickOf z' := hst.2.2 c (T.self_mem_stickOf c)
  have hdir : T.dir (nbr c (u + 5)) = u := by rw [T.dir_of_mem_stickOf hmem, hdz']
  obtain ⟨hhead, htail⟩ := T.head_tail_nbr_of_stackedBy h0n hst hu hdz'
  have hcc : walk (T.head c) u ((T.idx c - 1 : ℕ) : ℤ) = c := by
    have := T.cellOfStick_idx_sub_one c
    rwa [cellOfStick, hu] at this
  have hidx : T.idx (nbr c (u + 5)) = T.idx c := by
    have hlt' : T.idx c - 1 < n := by have := T.idx_le c; have := T.idx_pos c; omega
    have hc : T.cellOfStick z' (T.idx c - 1) = nbr c (u + 5) := by
      rw [cellOfStick, hdz', hhead, walk_nbr_comm, hcc]
    have h := T.cellOfStick_idx z' (T.idx c - 1) hlt'
    rw [hc] at h
    have := T.idx_pos c
    omega
  have hstick : T.stickOf (nbr c (u + 5)) = T.stickOf z' := T.stickOf_eq_of_mem hmem
  have hflank : T.flank u (nbr c (u + 5)) = nbr (T.flank u c) (u + 5) := by
    rw [T.flank_congr hstick, flank, flank, htail, nbr_comm]
  refine ⟨hdir, hidx, ?_, hflank, ?_⟩
  · exact SameStack.trans T hz' (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))
  · rw [hflank]
    have hdf : T.dir (T.flank u c) = u + 5 := T.dir_flank_eq hv hn hL hu
    have h := T.succ_idx (T.flank u c) hlt
    rw [hdf] at h
    exact h

/-- **Descending a block.**  Mirror image of `StickTiling.block_up`. -/
theorem block_down (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hgt : 1 < T.idx (T.flank u c)) :
    T.dir (nbr c (u + 2)) = u ∧ T.idx (nbr c (u + 2)) = T.idx c ∧
      T.SameStack c (nbr c (u + 2)) ∧
      T.flank u (nbr c (u + 2)) = nbr (T.flank u c) (u + 2) ∧
      T.idx (T.flank u (nbr c (u + 2))) = T.idx (T.flank u c) - 1 := by
  have h0n : 0 < n := by omega
  obtain ⟨z', hz', hst⟩ := T.exists_stackedBy_down' hv hn hL hu (T.sameStack_refl c)
    (by simpa [flank] using Nat.ne_of_gt hgt)
  have hdz' : T.dir z' = u := by
    rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn hL hz', hu]
  have hmem : nbr c (u + 2) ∈ T.stickOf z' := hst.2.2 c (T.self_mem_stickOf c)
  have hdir : T.dir (nbr c (u + 2)) = u := by rw [T.dir_of_mem_stickOf hmem, hdz']
  obtain ⟨hhead, htail⟩ := T.head_tail_nbr_of_stackedBy h0n hst hu hdz'
  have hcc : walk (T.head c) u ((T.idx c - 1 : ℕ) : ℤ) = c := by
    have := T.cellOfStick_idx_sub_one c
    rwa [cellOfStick, hu] at this
  have hidx : T.idx (nbr c (u + 2)) = T.idx c := by
    have hlt' : T.idx c - 1 < n := by have := T.idx_le c; have := T.idx_pos c; omega
    have hc : T.cellOfStick z' (T.idx c - 1) = nbr c (u + 2) := by
      rw [cellOfStick, hdz', hhead, walk_nbr_comm, hcc]
    have h := T.cellOfStick_idx z' (T.idx c - 1) hlt'
    rw [hc] at h
    have := T.idx_pos c
    omega
  have hstick : T.stickOf (nbr c (u + 2)) = T.stickOf z' := T.stickOf_eq_of_mem hmem
  have hflank : T.flank u (nbr c (u + 2)) = nbr (T.flank u c) (u + 2) := by
    rw [T.flank_congr hstick, flank, flank, htail, nbr_comm]
  refine ⟨hdir, hidx, ?_, hflank, ?_⟩
  · exact SameStack.trans T hz' (SameStack.symm T (T.sameStack_of_mem_stickOf hmem))
  · rw [hflank]
    have hdf : T.dir (T.flank u c) = u + 5 := T.dir_flank_eq hv hn hL hu
    have h := T.pred_idx (T.flank u c) hgt
    rw [hdf, opp_add_five] at h
    exact h

/-- **The cell above the top of a block starts a new block.**  If `c` is a cell of the topmost
stick of its block and the cell directly above it is horizontal, then that cell lies on the
bottommost stick of its own block. -/
theorem flank_idx_eq_one_of_top (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hidx : T.idx (T.flank u c) = n)
    (hd' : T.dir (nbr c (u + 5)) = u) (hL' : T.IsLeftLeaningStack (nbr c (u + 5))) :
    T.idx (T.flank u (nbr c (u + 5))) = 1 := by
  by_contra hne
  have hgt : 1 < T.idx (T.flank u (nbr c (u + 5))) :=
    lt_of_le_of_ne (T.idx_pos _) (Ne.symm hne)
  obtain ⟨-, -, -, -, hfi⟩ := T.block_down hv hn hL' hd' hgt
  rw [nbr_nbr_cancel c (opp_add_five u).symm] at hfi
  have := T.idx_le (T.flank u (nbr c (u + 5)))
  omega

end StickTiling

end StickPolyhex
