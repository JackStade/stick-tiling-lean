import Tiling.Proofs.WeaveBlocks

/-!
# The two sticks flanking a block

A block of a weave-pattern tiling — a left-leaning stack of horizontal sticks — is flanked by two
left-slanting sticks: the *back flank* `StickTiling.flank u c`, beyond the far ends of its
sticks, and the *front flank* `StickTiling.frontFlank u c`, beyond their near ends.

The main result of this file, `StickTiling.flank_idx_add`, says that the two flanking sticks
occupy exactly the rows of the block: the index of the back flank cell of a stick of the block
and the index of its front flank cell add up to `n + 1`.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- The cell just beyond the near end of the stick through `c`.  For a horizontal cell of a
weave-pattern tiling this is a cell of the left-slanting stick flanking its block in front. -/
def frontFlank (u : HexDir) (c : Hex) : Hex := nbr (T.head c) u.opp

/-- The direction of the stick flanking a left-leaning stack in front. -/
lemma dir_frontFlank (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c : Hex} {u : HexDir}
    (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) : T.dir (T.frontFlank u c) = u + 2 := by
  have h := (T.dir_beyond_ends_of_isLeftLeaningStack hv hn hL (T.sameStack_refl c)).2
  rw [hu] at h
  exact h

/-- The cell just beyond the near end of any stick of a left-leaning stack lies on the stick
flanking the stack in front. -/
lemma frontFlank_mem_of_sameStack (hv : T.SatisfiesWeaveRules) (hn : 2 ≤ n) {c z : Hex}
    {u : HexDir} (hL : T.IsLeftLeaningStack c) (hu : T.dir c = u) (hz : T.SameStack c z) :
    T.frontFlank u z ∈ T.stickOf (T.frontFlank u c) := by
  have h := T.head_nbr_mem_flank hv hn hL hu hz
  simpa [frontFlank, opp_eq_add_three] using h

/-- All the cells of a horizontal stick lie in the same row. -/
lemma shearRow_of_mem_stickOf_W {z x : Hex} (hd : T.dir z = HexDir.W) (hx : x ∈ T.stickOf z) :
    shearRow x = shearRow z := by
  rw [T.mem_stickOf_iff] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [cellOfStick, hd, shearRow_walk_W, (T.shear_head_W hd).2]

/-- **The two sticks flanking a block are aligned with it**: for a horizontal cell `c` of a
normalised weave-pattern tiling, the index of the cell beyond the far end of its stick and the
index of the cell beyond its near end add up to `n + 1`.  Both flanking sticks therefore occupy
exactly the rows of the block. -/
theorem flank_idx_add (hv : T.SatisfiesWeaveRules) (hn : 5 ≤ n)
    (hw : T.IsWeavePattern HexDir.W) {c : Hex} (hd : T.dir c = HexDir.W) :
    T.idx (T.flank HexDir.W c) + T.idx (T.frontFlank HexDir.W c) = n + 1 := by
  have h0n : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hL : T.IsLeftLeaningStack c := hw.horizontal_leftLeaning c hd
  have hdF : T.dir (T.flank HexDir.W c) = HexDir.NW := by
    have := T.dir_flank_eq hv hn2 hL hd
    simpa using this
  have hdG : T.dir (T.frontFlank HexDir.W c) = HexDir.SE := by
    have := T.dir_frontFlank hv hn2 hL hd
    simpa using this
  -- the two row identities, for every stick of the stack
  have key : ∀ z, T.SameStack c z →
      ((T.idx (T.flank HexDir.W z) : ℤ) + (T.idx (T.frontFlank HexDir.W z) : ℤ)) =
        shearRow (T.head (T.frontFlank HexDir.W c)) -
          shearRow (T.head (T.flank HexDir.W c)) + 2 := by
    intro z hz
    have hdz : T.dir z = HexDir.W := by
      rw [T.dir_eq_of_sameStack_of_isLeftLeaningStack hv hn2 hL hz, hd]
    -- the back flank cell of `z`
    have hmemF : T.flank HexDir.W z ∈ T.stickOf (T.flank HexDir.W c) :=
      T.flank_mem_of_sameStack hv hn2 hL hd hz
    have hheadF : T.head (T.flank HexDir.W z) = T.head (T.flank HexDir.W c) :=
      (T.mem_stickOf_iff_head_eq _ _).1 hmemF
    have hdF' : T.dir (T.flank HexDir.W z) = HexDir.NW := by
      rw [T.dir_of_mem_stickOf hmemF, hdF]
    have hrowF : shearRow (T.flank HexDir.W z) = shearRow z := by
      rw [flank, shearRow_nbr_W, T.shearRow_of_mem_stickOf_W hdz (T.tail_mem_stickOf h0n z)]
    have hA : shearRow z =
        shearRow (T.head (T.flank HexDir.W c)) + ((T.idx (T.flank HexDir.W z) : ℤ) - 1) := by
      have := (T.shear_head_NW hdF').2
      rw [hheadF, hrowF] at this
      omega
    -- the front flank cell of `z`
    have hmemG : T.frontFlank HexDir.W z ∈ T.stickOf (T.frontFlank HexDir.W c) :=
      T.frontFlank_mem_of_sameStack hv hn2 hL hd hz
    have hheadG : T.head (T.frontFlank HexDir.W z) = T.head (T.frontFlank HexDir.W c) :=
      (T.mem_stickOf_iff_head_eq _ _).1 hmemG
    have hdG' : T.dir (T.frontFlank HexDir.W z) = HexDir.SE := by
      rw [T.dir_of_mem_stickOf hmemG, hdG]
    have hrowG : shearRow (T.frontFlank HexDir.W z) = shearRow z := by
      rw [frontFlank, show HexDir.W.opp = HexDir.E from by decide, shearRow_nbr_E,
        T.shearRow_of_mem_stickOf_W hdz (T.head_mem_stickOf z)]
    have hB : shearRow z = shearRow (T.head (T.frontFlank HexDir.W c)) -
        ((T.idx (T.frontFlank HexDir.W z) : ℤ) - 1) := by
      have := (T.shear_head_SE hdG').2
      rw [hheadG, hrowG] at this
      omega
    omega
  -- the bottommost and the topmost stick of the block
  obtain ⟨y, hy, hyeq⟩ := T.exists_botStick hv hn2 hL hd
  obtain ⟨x, hx, hxeq⟩ := T.exists_topStick hv hn2 hL hd
  have hiy : T.idx (T.flank HexDir.W y) = 1 := by
    rw [flank, hyeq]
    exact T.idx_head _
  have hix : T.idx (T.flank HexDir.W x) = n := by
    rw [flank, hxeq]
    exact T.idx_tail h0n _
  have hky := key y hy
  have hkx := key x hx
  rw [hiy] at hky
  rw [hix] at hkx
  have h1 := T.idx_le (T.frontFlank HexDir.W y)
  have h2 := T.idx_pos (T.frontFlank HexDir.W x)
  have hkc := key c (T.sameStack_refl c)
  omega

end StickTiling

end StickPolyhex
