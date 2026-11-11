import Tiling.Proofs.WeaveShear

/-!
# Left-slanting sticks of a normalised weave-pattern tiling

In a tiling normalised so that its horizontal sticks point west, the left-slanting sticks point
north-west (the right part of a gap, whose arrows point left) or south-east (the left part of a
gap, whose arrows point right).  In sheared coordinates such a stick occupies `n` consecutive
rows of a single column.

This file introduces the lowest and the highest cell of a left-slanting stick
(`StickTiling.botCell`, `StickTiling.topCell`) and proves the two facts that pin such a stick
down inside the weave pattern: the cell directly below its lowest cell and the cell directly
above its highest cell are horizontal cells of left-leaning stacks
(`StickTiling.dir_nbr_below_botCell`, `StickTiling.dir_nbr_above_topCell`).
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- A cell lies on a left-slanting stick. -/
def Slanted (c : Hex) : Prop := T.dir c = HexDir.NW ∨ T.dir c = HexDir.SE

/-- The lowest cell of the stick through `c`, for a left-slanting stick. -/
def botCell (c : Hex) : Hex := if T.dir c = HexDir.NW then T.head c else T.tail c

/-- The highest cell of the stick through `c`, for a left-slanting stick. -/
def topCell (c : Hex) : Hex := if T.dir c = HexDir.NW then T.tail c else T.head c

lemma botCell_of_NW {c : Hex} (h : T.dir c = HexDir.NW) : T.botCell c = T.head c := by
  rw [botCell, if_pos h]

lemma botCell_of_SE {c : Hex} (h : T.dir c = HexDir.SE) : T.botCell c = T.tail c := by
  rw [botCell, if_neg (by rw [h]; decide)]

lemma topCell_of_NW {c : Hex} (h : T.dir c = HexDir.NW) : T.topCell c = T.tail c := by
  rw [topCell, if_pos h]

lemma topCell_of_SE {c : Hex} (h : T.dir c = HexDir.SE) : T.topCell c = T.head c := by
  rw [topCell, if_neg (by rw [h]; decide)]

lemma botCell_mem_stickOf (hn : 0 < n) (c : Hex) : T.botCell c ∈ T.stickOf c := by
  rw [botCell]
  split
  · exact T.head_mem_stickOf c
  · exact T.tail_mem_stickOf hn c

lemma topCell_mem_stickOf (hn : 0 < n) (c : Hex) : T.topCell c ∈ T.stickOf c := by
  rw [topCell]
  split
  · exact T.tail_mem_stickOf hn c
  · exact T.head_mem_stickOf c

lemma dir_botCell (hn : 0 < n) (c : Hex) : T.dir (T.botCell c) = T.dir c :=
  T.dir_of_mem_stickOf (T.botCell_mem_stickOf hn c)

lemma dir_topCell (hn : 0 < n) (c : Hex) : T.dir (T.topCell c) = T.dir c :=
  T.dir_of_mem_stickOf (T.topCell_mem_stickOf hn c)

/-- The index of the lowest cell of a left-slanting stick. -/
lemma idx_botCell (hn : 0 < n) {c : Hex} (hs : T.Slanted c) :
    T.idx (T.botCell c) = if T.dir c = HexDir.NW then 1 else n := by
  rcases hs with h | h
  · rw [botCell_of_NW T h, if_pos h, T.idx_head c]
  · rw [botCell_of_SE T h, if_neg (by rw [h]; decide), T.idx_tail hn c]

/-- The index of the highest cell of a left-slanting stick. -/
lemma idx_topCell (hn : 0 < n) {c : Hex} (hs : T.Slanted c) :
    T.idx (T.topCell c) = if T.dir c = HexDir.NW then n else 1 := by
  rcases hs with h | h
  · rw [topCell_of_NW T h, if_pos h, T.idx_tail hn c]
  · rw [topCell_of_SE T h, if_neg (by rw [h]; decide), T.idx_head c]

/-- A cell whose index is the last one is the far end of its stick. -/
lemma tail_eq_self_of_idx_eq {z : Hex} (hi : T.idx z = n) : T.tail z = z := by
  have h := T.cellOfStick_idx_sub_one z
  rwa [hi] at h

/-- A cell whose index is `1` is the near end of its stick. -/
lemma head_eq_self_of_idx_eq {z : Hex} (hi : T.idx z = 1) : T.head z = z := by
  rw [head, hi]
  simp

/-- The lowest cell of a left-slanting stick is the one recognised by
`StickTiling.SlantEndAbove`. -/
lemma botCell_eq_self_of_slantEndAbove {z : Hex}
    (h : T.SlantEndAbove HexDir.W z) : T.botCell z = z := by
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · rw [botCell_of_SE T (by simpa using hd), T.tail_eq_self_of_idx_eq hi]
  · rw [botCell_of_NW T (by simpa using hd), T.head_eq_self_of_idx_eq hi]

/-- The highest cell of a left-slanting stick is the one recognised by
`StickTiling.SlantEndBelow`. -/
lemma topCell_eq_self_of_slantEndBelow {z : Hex}
    (h : T.SlantEndBelow HexDir.W z) : T.topCell z = z := by
  rcases h with ⟨hd, hi⟩ | ⟨hd, hi⟩
  · rw [topCell_of_SE T (by simpa using hd), T.head_eq_self_of_idx_eq hi]
  · rw [topCell_of_NW T (by simpa using hd), T.tail_eq_self_of_idx_eq hi]

/-- The cells of a left-slanting stick are obtained by climbing from its lowest cell. -/
lemma stickOf_eq_image_botCell (hn : 0 < n) {c : Hex} (hs : T.Slanted c) :
    T.stickOf c = (Finset.range n).image fun k : ℕ => walk (T.botCell c) HexDir.NW (k : ℤ) := by
  have hslant : T.SlantEndAbove HexDir.W (T.botCell c) := by
    rcases hs with h | h
    · refine Or.inr ⟨by simpa using T.dir_botCell hn c ▸ h, ?_⟩
      rw [botCell_of_NW T h, T.idx_head c]
    · refine Or.inl ⟨by simpa using T.dir_botCell hn c ▸ h, ?_⟩
      rw [botCell_of_SE T h, T.idx_tail hn c]
  have h := T.stickOf_eq_image_of_slantEndAbove hslant
  rw [T.stickOf_eq_of_mem (T.botCell_mem_stickOf hn c)] at h
  simpa using h

/-- The lowest cell of a left-slanting stick is the same for all its cells. -/
lemma botCell_congr {c c' : Hex} (h : T.stickOf c = T.stickOf c') : T.botCell c = T.botCell c' := by
  have hhead : T.head c = T.head c' := by
    have hmem : c ∈ T.stickOf c' := by rw [← h]; exact T.self_mem_stickOf c
    exact (T.mem_stickOf_iff_head_eq c' c).1 hmem
  have hdir : T.dir c = T.dir c' := by
    rw [← T.dir_head c, ← T.dir_head c', hhead]
  rw [botCell, botCell, hdir, tail, tail, cellOfStick, cellOfStick, hhead, hdir]

lemma topCell_congr {c c' : Hex} (h : T.stickOf c = T.stickOf c') : T.topCell c = T.topCell c' := by
  have hhead : T.head c = T.head c' := by
    have hmem : c ∈ T.stickOf c' := by rw [← h]; exact T.self_mem_stickOf c
    exact (T.mem_stickOf_iff_head_eq c' c).1 hmem
  have hdir : T.dir c = T.dir c' := by
    rw [← T.dir_head c, ← T.dir_head c', hhead]
  rw [topCell, topCell, hdir, tail, tail, cellOfStick, cellOfStick, hhead, hdir]

/-! ### The cells beyond the ends of a left-slanting stick -/

/-- **The cell directly below the lowest cell of a left-slanting stick is horizontal.**  This is
the statement that every left-slanting stick of the weave pattern rests on a block. -/
theorem holeAbove_of_slanted (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {c : Hex} (hs : T.Slanted c) :
    T.HoleAbove HexDir.W c := by
  obtain ⟨c₀, hd₀⟩ := hw.exists_horizontal
  have hanch := T.anchored_all hv hn hd₀ (hw.horizontal_leftLeaning c₀ hd₀) c
  rcases hanch with ⟨hd, -⟩ | h | h
  · exfalso
    rcases hs with h | h <;> rw [hd] at h <;> exact absurd h (by decide)
  · exact h
  · exact T.holeAbove_of_holeBelow hv hn h

theorem dir_nbr_below_botCell (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {c : Hex} (hs : T.Slanted c) :
    T.dir (nbr (T.botCell c) HexDir.SE) = HexDir.W := by
  have h0n : 0 < n := by omega
  obtain ⟨p, hdp, hLp, hslant, hmem⟩ := T.holeAbove_of_slanted hv hn hw hs
  have hbot : T.botCell c = nbr p HexDir.NW := by
    rw [T.botCell_congr (T.stickOf_eq_of_mem hmem)]
    simpa using T.botCell_eq_self_of_slantEndAbove (by simpa using hslant)
  rw [hbot, nbr_nbr_cancel p (by decide : HexDir.SE = HexDir.NW.opp)]
  exact hdp

/-- **The cell directly above the highest cell of a left-slanting stick is horizontal.** -/
theorem dir_nbr_above_topCell (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {c : Hex} (hs : T.Slanted c) :
    T.dir (nbr (T.topCell c) HexDir.NW) = HexDir.W := by
  have h0n : 0 < n := by omega
  obtain ⟨p, hdp, hLp, hslant, hmem⟩ :=
    T.holeBelow_of_holeAbove hv hn (T.holeAbove_of_slanted hv hn hw hs)
  have htop : T.topCell c = nbr p HexDir.SE := by
    rw [T.topCell_congr (T.stickOf_eq_of_mem hmem)]
    simpa using T.topCell_eq_self_of_slantEndBelow (by simpa using hslant)
  rw [htop, nbr_nbr_cancel p (by decide : HexDir.NW = HexDir.SE.opp)]
  exact hdp

end StickTiling

end StickPolyhex
