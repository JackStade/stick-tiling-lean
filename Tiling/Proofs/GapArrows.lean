import Tiling.Proofs.GapConditions

/-!
# What the marks say about the gaps

This file translates each clause of `Schematic.RespectsMarking` for the marking
`GapSpec.marking` into a statement about a gap of the schematic.

* `topArrowL_effect`, `topArrowR_effect`: an arrow mark on the top face at the position `p`
  cannot lie strictly inside the left (resp. right) part of a gap of the row above, in the
  precise sense made explicit below;
* `botArrowL_effect`, `botArrowR_effect`: the same for the bottom face and the gap of the row
  below a block;
* `triangleR_of_gap`, `triangleL_of_gap`: the two ends of a gap sit above triangle marks.

Throughout, a gap of the row `r` lying above the columns `j, …, j + l + m - 1` of a block of the
row `r - 1` has its *left end* at the position `j - 2` of that block, its *right end* at the
position `j + l + m - 2`, and its change of direction at the position `j + l - 2`.
-/

namespace StickPolyhex

namespace Schematic

variable {G : GapSpec} {S : Schematic G.blockLen}

/-! ### The arrows of the top face -/

/-- A left-facing arrow mark on the top face at the position `p` cannot satisfy
`j - 1 ≤ p ≤ j + l - 2` for a gap of the row above lying above the columns `j, …` of the
block. -/
lemma topArrowL_effect (hM : S.RespectsMarking G.marking) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) {p : ℕ} (hp : p ∈ G.marking.topArrowL)
    (h1 : (j : ℤ) - 1 ≤ p) (h2 : (p : ℤ) ≤ (j : ℤ) + l - 2) : False := by
  have hm := hg.toGapAt.m_pos
  have hbelow := hg.below (c := p + 1 - j) (by omega)
  have hgapL := hg.toGapAt.slot_gapL (k := p + 1 - j) (by omega)
  refine hM.topArrowL hp (r - 1) (u + ((p + 1 - j : ℕ) : ℤ)) ?_ ?_
  · rw [hbelow]; congr 1; omega
  · rw [show r - 1 + 1 = r by ring]; exact hgapL

/-- A right-facing arrow mark on the top face at the position `p` cannot satisfy
`j + l - 2 ≤ p ≤ j + l + m - 3` for a gap of the row above. -/
lemma topArrowR_effect (hM : S.RespectsMarking G.marking) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) {p : ℕ} (hp : p ∈ G.marking.topArrowR)
    (h1 : (j : ℤ) + l - 2 ≤ p) (h2 : (p : ℤ) ≤ (j : ℤ) + l + m - 3) : False := by
  have hl := hg.toGapAt.l_pos
  have hbelow := hg.below (c := p + 2 - j) (by omega)
  have hgapR := hg.toGapAt.slot_gapR (k := p + 2 - j - l) (by omega)
  refine hM.topArrowR hp (r - 1) (u + ((p + 2 - j : ℕ) : ℤ)) ?_ ?_
  · rw [hbelow]; congr 1; omega
  · rw [show r - 1 + 1 = r by ring]
    rw [show u + ((p + 2 - j : ℕ) : ℤ) = u + (l : ℤ) + ((p + 2 - j - l : ℕ) : ℤ) by
      omega]
    exact hgapR

/-! ### The arrows of the bottom face -/

/-- A left-facing arrow mark on the bottom face at the position `p` of a block starting at the
column `c` cannot lie above the left part of the gap of the row below. -/
lemma botArrowL_effect (hM : S.RespectsMarking G.marking) {r c u' : ℤ} {l' m' : ℕ}
    (hc : S.slot r c = .block 0) (h' : S.GapAt (r - 1) u' l' m')
    {p : ℕ} (hp : p ∈ G.marking.botArrowL)
    (h1 : u' ≤ c + p) (h2 : c + (p : ℤ) ≤ u' + l' - 1)
    (he : u' + l' + m' - 1 ≤ c + G.blockLen) : False := by
  have hm := h'.m_pos
  have hblock : S.slot r (c + p) = .block p := by
    have := S.slot_of_start hc (y := c + p) (by omega) (by omega)
    rw [this]; congr 1; omega
  have hgapL := h'.slot_gapL (k := (c + (p : ℤ) - u').toNat) (by omega)
  refine hM.botArrowL hp r (c + p) hblock ?_
  rw [show r - 1 = r - 1 by rfl]
  rw [show c + (p : ℤ) = u' + (((c + (p : ℤ) - u').toNat : ℕ) : ℤ) by omega]
  exact hgapL

/-- A right-facing arrow mark on the bottom face at the position `p` of a block starting at the
column `c` cannot lie above the right part of the gap of the row below. -/
lemma botArrowR_effect (hM : S.RespectsMarking G.marking) {r c u' : ℤ} {l' m' : ℕ}
    (hc : S.slot r c = .block 0) (h' : S.GapAt (r - 1) u' l' m')
    {p : ℕ} (hp : p ∈ G.marking.botArrowR)
    (h1 : u' + l' ≤ c + (p : ℤ) + 1) (h2 : c + (p : ℤ) + 1 ≤ u' + l' + m' - 1)
    (he : u' + l' + m' - 1 ≤ c + G.blockLen) : False := by
  have hblock : S.slot r (c + p + 1) = .block (p + 1) := by
    have := S.slot_of_start hc (y := c + (p : ℤ) + 1) (by omega) (by omega)
    rw [this]; congr 1; omega
  have hgapR := h'.slot_gapR (k := (c + (p : ℤ) + 1 - u' - l').toNat) (by omega)
  refine hM.botArrowR hp r (c + p + 1) hblock ?_
  rw [show c + (p : ℤ) + 1 = u' + (l' : ℤ) + (((c + (p : ℤ) + 1 - u' - l').toNat : ℕ) : ℤ) by
    omega]
  exact hgapR

/-! ### The triangles -/

/-- The left end of a gap sits above a right-facing triangle mark. -/
lemma triangleR_of_gap (hM : S.RespectsMarking G.marking) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) : (j - 2) ∈ G.marking.triangleR := by
  have hj2 := hg.two_le
  refine hM.triangleR (j - 2) (r - 1) (u - 1) ?_ ?_
  · have h1 : S.slot (r - 1) (u - 1 + 1) = .block (j - 1 + 1) := by
      rw [show u - 1 + 1 = u by ring, hg.slot_below]; congr 1; omega
    have := S.pred_of_block_succ h1
    rw [this]; congr 1; omega
  · rw [show r - 1 + 1 = r by ring]; exact hg.toGapAt.blockLeft

/-- The right end of a gap sits above a left-facing triangle mark. -/
lemma triangleL_of_gap (hM : S.RespectsMarking G.marking) {r u : ℤ} {l m j : ℕ}
    (hg : S.GapData r u l m j) : (j + l + m - 2) ∈ G.marking.triangleL := by
  have hj2 := hg.two_le
  have hl := hg.toGapAt.l_pos
  have hm := hg.toGapAt.m_pos
  refine hM.triangleL (j + l + m - 2) (r - 1) (u + ((l + m - 1 : ℕ) : ℤ)) ?_ ?_
  · have := hg.below (c := l + m - 1) (by omega)
    rw [this]; congr 1; omega
  · rw [show r - 1 + 1 = r by ring,
      show u + ((l + m - 1 : ℕ) : ℤ) + 1 = u + (l : ℤ) + (m : ℤ) by omega]
    exact hg.toGapAt.blockRight

end Schematic

end StickPolyhex
