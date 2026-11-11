import Tiling.Proofs.ABForward
import Tiling.Proofs.ABReverse
import Tiling.Proofs.GapRealization

/-!
# The reduction of Sections 2.6–2.8

This file states the main result of Sections 2.6–2.8 of the paper: given any set of AB tiles one
can compute the data of Section 2.5 — the number `s` of buckets, the number `v` of values and,
for every bucket `i`, the sets `L i`, `R i` of left and right values and the interval `I i` —
in such a way that the resulting gap conditions can be satisfied exactly when the AB tiles tile
the plane.

The data is the `GapSpec` produced by `ABSim.ABData.spec` from the numbers extracted by
`ABSim.abData`; for a degenerate tile set (one of the two lists being empty, so that no tiling
exists at all) the unsatisfiable specification `ABSim.emptyGapSpec` is used instead.

* `ABSim.exists_gapSpec_iff_abTilesPlane` is the statement asked for: there are `n`
  (the number of values, called `v` here), `s`, and the sets and intervals, such that a valid gap
  assignment exists if and only if the tile set admits a tiling.
* `ABSim.exists_gapSpec_tiling_of_abTilesPlane` combines it with the realisation theorem of
  Section 2.5: whenever the AB tiles tile the plane, the marked stick built from that data admits
  a weave-pattern tiling of the plane respecting its marking.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB

/-! ### A specification which nothing satisfies -/

/-- The specification with one bucket, one value and no allowed value at all: no gap assignment
satisfies it. -/
def emptyGapSpec : GapSpec where
  s := 1
  v := 1
  hs := le_refl 1
  hv := le_refl 1
  L := fun _ => ∅
  R := fun _ => ∅
  hL := fun _ => Set.empty_subset _
  hR := fun _ => Set.empty_subset _
  Imin := fun _ => 0
  Imax := fun _ => 0
  hImin := by intro i; norm_num
  hImax := by intro i; norm_num
  hI := fun _ => le_refl 0

lemma not_nonempty_gapAssignment_emptyGapSpec : ¬ Nonempty (GapAssignment emptyGapSpec) := by
  rintro ⟨A⟩
  exact (A.x_mem 0 0 : A.xv 0 0 ∈ (∅ : Set ℤ))

/-! ### A tiling uses tiles of both kinds -/

lemma abTilesPlane_A_ne (S : ABTileSet) (h : ABTilesPlane S) : S.A ≠ [] := by
  obtain ⟨t, ht⟩ := h
  intro hnil
  have := ht.memA 0 0 ⟨0, by ring⟩
  rw [hnil] at this
  exact List.not_mem_nil this

lemma abTilesPlane_B_ne (S : ABTileSet) (h : ABTilesPlane S) : S.B ≠ [] := by
  obtain ⟨t, ht⟩ := h
  intro hnil
  have hodd : ¬ Even (1 : ℤ) := by decide
  have := ht.memB 1 0 hodd
  rw [hnil] at this
  exact List.not_mem_nil this

/-! ### The reduction -/

/-- **Sections 2.6–2.8 of the paper.**  For every set of AB tiles there are a number of values, a
number of buckets, and sets of left and right values and intervals for each bucket — that is, a
`GapSpec` — whose gap conditions can be satisfied exactly when the tile set admits a tiling of
the plane. -/
theorem exists_gapSpec_iff_abTilesPlane (S : ABTileSet) :
    ∃ G : GapSpec, (Nonempty (GapAssignment G) ↔ ABTilesPlane S) := by
  by_cases hA : S.A = []
  · refine ⟨emptyGapSpec, ⟨fun h => absurd h not_nonempty_gapAssignment_emptyGapSpec, ?_⟩⟩
    intro h
    exact absurd hA (abTilesPlane_A_ne S h)
  by_cases hB : S.B = []
  · refine ⟨emptyGapSpec, ⟨fun h => absurd h not_nonempty_gapAssignment_emptyGapSpec, ?_⟩⟩
    intro h
    exact absurd hB (abTilesPlane_B_ne S h)
  refine ⟨(abData S hA).spec, ?_⟩
  constructor
  · intro h
    exact (nonempty_indexTiling_iff_abTilesPlane hA hB).1
      (nonempty_indexTiling_of_gapAssignment _ h)
  · intro h
    obtain ⟨T⟩ := (nonempty_indexTiling_iff_abTilesPlane hA hB).2 h
    exact nonempty_gapAssignment_of_indexTiling T

/-- The same specification, carried over to the sticks of Section 2.5: whenever the AB tiles
tile the plane, the marked stick built from the specification admits a weave-pattern tiling of
the plane respecting its marking. -/
theorem exists_gapSpec_tiling_of_abTilesPlane (S : ABTileSet) :
    ∃ G : GapSpec, (Nonempty (GapAssignment G) ↔ ABTilesPlane S) ∧
      (ABTilesPlane S → ∃ T : StickTiling (G.blockLen + 1),
        T.SatisfiesRules (markedRules G.blockLen G.marking) ∧ T.FormsWeavePattern) := by
  obtain ⟨G, hG⟩ := exists_gapSpec_iff_abTilesPlane S
  refine ⟨G, hG, fun h => ?_⟩
  obtain ⟨A⟩ := hG.2 h
  exact GapSpec.exists_tiling_of_gapAssignment A

end ABSim

end StickPolyhex
