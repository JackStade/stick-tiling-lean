import Tiling.Proofs.Prelude
import Tiling.MainResults.ABTiling
/-!
# AB tiling, and the reduction from Wang tiling (Section 2.2 of the paper)

In the *AB tiling* problem one is given two finite sets `A` and `B` of `1 × 2` (one wide, two
tall) rectangular tiles.  Each tile carries four colors: on its left long edge a top and a bottom
color, and likewise on its right long edge.  The question is whether the plane can be tiled,
without rotating tiles, so that

* every `A` tile is placed with its lower-left corner at a point with **even** `x`- and
  `y`-coordinates,
* every `B` tile is placed with its lower-left corner at a point with **odd** `x`- and
  `y`-coordinates, and
* the colors agree along every vertical edge.

Such a placement is completely rigid: in an even column `x` the dominoes occupy the pairs of rows
`{2k, 2k+1}`, and in an odd column they occupy the pairs `{2k+1, 2k+2}`.  We therefore represent a
placement by a function `t : ℤ → ℤ → ABTile`, where `t x k` is the tile in column `x` whose
lower-left corner is at height `2 * k` if `x` is even and at height `2 * k + 1` if `x` is odd
(`ABTiling.tileHeight`).  The four color-matching conditions along the vertical edges are the
fields `matchEvenLow`, `matchEvenHigh`, `matchOddLow`, `matchOddHigh` of `ValidABTiling`; each of
them equates the color of the right edge of a tile with the color of the left edge of its
horizontal neighbour along one unit segment.

The main result is Lemma 5 of the paper, in the effective form that makes it a proof of
undecidability of AB tiling: the map `reduceAB`, sending a Wang tileset to an AB tileset, is
computable and satisfies `TilesPlane T ↔ ABTilesPlane (reduceAB T)`; hence Wang tiling is
many-one reducible to AB tiling (`wang_manyOneReducible_abTiling`).

The construction of `reduceAB` is the one in the paper: the `i`-th Wang tile, with colors
`a, b, c, d` on its left, right, upper and lower faces, gives one `A` tile with colors
`0, c, a, link i` and one `B` tile with colors `link i, b, d, 0` on its upper-left, upper-right,
lower-left and lower-right faces, where `link i` is a color used by no other pair of tiles.  The
two tiles are then forced to occur together, forming an S-tetromino that represents one Wang tile.
Here we take `link t = 2 * (encoding of t) + 2` and rename a Wang color `c` to `2 * c + 1`; this
only renames the colors of the paper's construction, and keeps the three groups of colors
(`0`, the Wang colors, the linking colors) disjoint without having to compute the largest color
of the tileset.

The Wang-tiling side of the statement (`WangTile`, `TileSet`, `WangTile.HMatches`,
`WangTile.VMatches`, `ValidPlaneTiling`, `TilesPlane`) is *not* developed here: it is imported
from the `lean-wang` project (<https://github.com/edemaine/lean-wang>), which this project
declares as a Lake dependency; the declarations used are those of its `LeanWang.Basic`.
Everything in the present file is original to this project.
-/

namespace Tiling.AB

open LeanWang

/-! ## The reduction -/

/-- The AB color representing the Wang color `c`. -/
def wangColor (c : ℕ) : ℕ := 2 * c + 1

/-- The AB color linking the two tiles built from a Wang tile; it occurs on exactly one `A` tile
and one `B` tile, which are therefore forced to occur together. -/
def linkColor (t : WangTile) : ℕ := 2 * Encodable.encode t + 2

/-- The `A` tile built from a Wang tile. -/
def toA (t : WangTile) : ABTile where
  ul := 0
  ur := wangColor t.n
  ll := wangColor t.w
  lr := linkColor t

/-- The `B` tile built from a Wang tile. -/
def toB (t : WangTile) : ABTile where
  ul := linkColor t
  ur := wangColor t.e
  ll := wangColor t.s
  lr := 0

/-- The reduction: the AB tileset simulating a Wang tileset. -/
def reduceAB (T : TileSet) : ABTileSet where
  A := T.map toA
  B := T.map toB

theorem wangColor_injective : Function.Injective wangColor := by
  intro a b h
  simpa [wangColor] using h

theorem linkColor_injective : Function.Injective linkColor := by
  intro a b h
  have : Encodable.encode a = Encodable.encode b := by
    simpa [linkColor] using h
  exact Encodable.encode_injective this

theorem toA_injective : Function.Injective toA := by
  intro a b h
  exact linkColor_injective (congrArg ABTile.lr h)

theorem toB_injective : Function.Injective toB := by
  intro a b h
  exact linkColor_injective (congrArg ABTile.ul h)

/-- The two sets of the AB tileset produced by the reduction have the same size, as required in
the statement of the AB tiling problem. -/
theorem reduceAB_length (T : TileSet) : (reduceAB T).A.length = (reduceAB T).B.length := by
  simp [reduceAB]

/-! ## Correctness of the reduction -/

private theorem even_two_mul (j : ℤ) : Even (2 * j) := ⟨j, by ring⟩

private theorem not_even_two_mul_add_one (j : ℤ) : ¬ Even (2 * j + 1) := by
  rintro ⟨m, hm⟩
  omega

/-- From an AB tiling of the tileset produced by the reduction we read off a Wang tiling: the
tile of the `A` set placed in column `2 * j` at index `y` is `toA` of a Wang tile, and that Wang
tile is put at position `(j, y)`. -/
theorem tilesPlane_of_abTilesPlane (T : TileSet) :
    ABTilesPlane (reduceAB T) → TilesPlane T := by
  rintro ⟨t, ht⟩
  have hA : ∀ j k : ℤ, ∃ u : TileIn T, toA u.1 = t (2 * j) k := by
    intro j k
    have hmem := ht.memA (2 * j) k (even_two_mul j)
    simp only [reduceAB, List.mem_map] at hmem
    obtain ⟨u, hu, huu⟩ := hmem
    exact ⟨⟨u, hu⟩, huu⟩
  have hB : ∀ j k : ℤ, ∃ u : TileIn T, toB u.1 = t (2 * j + 1) k := by
    intro j k
    have hmem := ht.memB (2 * j + 1) k (not_even_two_mul_add_one j)
    simp only [reduceAB, List.mem_map] at hmem
    obtain ⟨u, hu, huu⟩ := hmem
    exact ⟨⟨u, hu⟩, huu⟩
  choose w hw using hA
  choose v hv using hB
  -- The `B` tile in column `2 * j + 1` at index `k` comes from the same Wang tile as the `A`
  -- tile in column `2 * j` at index `k + 1`: together they form an S-tetromino.
  have hlink : ∀ j k : ℤ, (v j k).1 = (w j (k + 1)).1 := by
    intro j k
    have h := ht.matchEvenHigh (2 * j) k (even_two_mul j)
    rw [← hw j (k + 1), ← hv j k] at h
    simp only [toA, toB] at h
    exact (linkColor_injective h).symm
  refine ⟨fun p => w p.1 p.2, ?_, ?_⟩
  · rintro ⟨j, y⟩
    show (w j y).1.e = (w (j + 1) y).1.w
    have h := ht.matchOddHigh (2 * j + 1) (y - 1) (not_even_two_mul_add_one j)
    have hcol : (2 * j + 1 + 1 : ℤ) = 2 * (j + 1) := by ring
    have hrow : (y - 1 + 1 : ℤ) = y := by ring
    rw [hcol, hrow, ← hw (j + 1) y, ← hv j (y - 1)] at h
    simp only [toA, toB] at h
    have := wangColor_injective h
    rw [hlink j (y - 1), hrow] at this
    exact this
  · rintro ⟨j, y⟩
    show (w j y).1.n = (w j (y + 1)).1.s
    have h := ht.matchEvenLow (2 * j) y (even_two_mul j)
    rw [← hw j y, ← hv j y] at h
    simp only [toA, toB] at h
    have := wangColor_injective h
    rw [hlink j y] at this
    exact this

/-- From a Wang tiling we build an AB tiling of the reduced tileset: the Wang tile at position
`(j, y)` becomes the `A` tile in column `2 * j` at index `y` together with the `B` tile in column
`2 * j + 1` at index `y - 1`. -/
theorem abTilesPlane_of_tilesPlane (T : TileSet) :
    TilesPlane T → ABTilesPlane (reduceAB T) := by
  rintro ⟨w, hH, hV⟩
  refine ⟨fun x k => if Even x then toA (w (x / 2, k)).1 else toB (w (x / 2, k + 1)).1, ?_⟩
  have hdiv0 : ∀ j : ℤ, (2 * j) / 2 = j := by intro j; omega
  have hdiv1 : ∀ j : ℤ, (2 * j + 1) / 2 = j := by intro j; omega
  constructor
  · intro x k hx
    simp only [if_pos hx, reduceAB]
    exact List.mem_map_of_mem (w _).2
  · intro x k hx
    simp only [if_neg hx, reduceAB]
    exact List.mem_map_of_mem (w _).2
  · intro x k hx
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, x = 2 * j := by
      obtain ⟨m, hm⟩ := hx; exact ⟨m, by omega⟩
    simp only [if_pos (even_two_mul j), if_neg (not_even_two_mul_add_one j), hdiv0, hdiv1,
      toA, toB]
    exact congrArg wangColor (hV (j, k))
  · intro x k hx
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, x = 2 * j := by
      obtain ⟨m, hm⟩ := hx; exact ⟨m, by omega⟩
    simp only [if_pos (even_two_mul j), if_neg (not_even_two_mul_add_one j), hdiv0, hdiv1,
      toA, toB]
  · intro x k hx
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, x = 2 * j + 1 := by
      obtain ⟨m, hm⟩ := Int.not_even_iff_odd.mp hx
      exact ⟨m, hm⟩
    have hcol : (2 * j + 1 + 1 : ℤ) = 2 * (j + 1) := by ring
    simp only [hcol, if_pos (even_two_mul (j + 1)), if_neg (not_even_two_mul_add_one j),
      hdiv0, hdiv1, toA, toB]
  · intro x k hx
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, x = 2 * j + 1 := by
      obtain ⟨m, hm⟩ := Int.not_even_iff_odd.mp hx
      exact ⟨m, hm⟩
    have hcol : (2 * j + 1 + 1 : ℤ) = 2 * (j + 1) := by ring
    simp only [hcol, if_pos (even_two_mul (j + 1)), if_neg (not_even_two_mul_add_one j),
      hdiv0, hdiv1, toA, toB]
    exact congrArg wangColor (hH (j, k + 1))

/-- **Correctness of the reduction.**  A Wang tileset tiles the plane if and only if the AB
tileset produced from it admits an AB tiling of the plane. -/
theorem tilesPlane_iff_abTilesPlane (T : TileSet) :
    TilesPlane T ↔ ABTilesPlane (reduceAB T) :=
  ⟨abTilesPlane_of_tilesPlane T, tilesPlane_of_abTilesPlane T⟩

/-! ## Computability of the reduction -/

theorem wangColor_primrec : Primrec wangColor :=
  (Primrec.succ.comp Primrec.nat_double).of_eq fun _ => rfl

theorem linkColor_primrec : Primrec linkColor :=
  (Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_double.comp Primrec.encode))).of_eq
    fun _ => rfl

theorem toA_primrec : Primrec toA := by
  have hf : Primrec (fun t : WangTile => ((0 : ℕ), wangColor t.n, wangColor t.w, linkColor t)) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.pair (wangColor_primrec.comp WangTile.n_primrec)
        (Primrec.pair (wangColor_primrec.comp WangTile.w_primrec) linkColor_primrec))
  have h := (Primrec.of_equiv_symm_iff (e := ABTile.equivTuple)
    (f := fun t : WangTile => ((0 : ℕ), wangColor t.n, wangColor t.w, linkColor t))).2 hf
  exact h.of_eq fun t => by cases t; rfl

theorem toB_primrec : Primrec toB := by
  have hf : Primrec (fun t : WangTile => (linkColor t, wangColor t.e, wangColor t.s, (0 : ℕ))) :=
    Primrec.pair linkColor_primrec
      (Primrec.pair (wangColor_primrec.comp WangTile.e_primrec)
        (Primrec.pair (wangColor_primrec.comp WangTile.s_primrec) (Primrec.const 0)))
  have h := (Primrec.of_equiv_symm_iff (e := ABTile.equivTuple)
    (f := fun t : WangTile => (linkColor t, wangColor t.e, wangColor t.s, (0 : ℕ)))).2 hf
  exact h.of_eq fun t => by cases t; rfl

/-- The reduction is computable. -/
theorem reduceAB_computable : Computable reduceAB := by
  have hg : Primrec (fun T : TileSet => (T.map toA, T.map toB)) :=
    Primrec.pair (Primrec.list_map Primrec.id (toA_primrec.comp Primrec.snd))
      (Primrec.list_map Primrec.id (toB_primrec.comp Primrec.snd))
  have h := (Primrec.of_equiv_symm_iff (e := ABTileSet.equivProd)
    (f := fun T : TileSet => (T.map toA, T.map toB))).2 hg
  exact (h.of_eq fun _ => rfl).to_comp

/-- **Lemma 5 of the paper, in effective form**: Wang tiling is many-one reducible to AB tiling.
Consequently AB tiling is undecidable. -/
theorem wang_manyOneReducible_abTiling : ManyOneReducible TilesPlane ABTilesPlane :=
  ⟨reduceAB, reduceAB_computable, tilesPlane_iff_abTilesPlane⟩

/-- Sanity check that the notions above are not vacuous: the Wang tileset consisting of the single
tile all of whose colors are `0` tiles the plane, so the AB tileset built from it does admit an
AB tiling of the plane. -/
example : ABTilesPlane (reduceAB [⟨0, 0, 0, 0⟩]) := by
  rw [← tilesPlane_iff_abTilesPlane]
  exact ⟨fun _ => ⟨⟨0, 0, 0, 0⟩, by simp⟩, fun _ => rfl, fun _ => rfl⟩

end Tiling.AB
