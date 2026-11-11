import LeanWang.Basic

/-!
# Wang tiling: the imported definition, expanded for review

The authoritative Wang types and their encodings come from the pinned `lean-wang`
dependency, `LeanWang/Basic.lean`. They are reused, not replaced by a second model:

```
structure WangTile where
  n : Nat  -- north color
  s : Nat  -- south color
  e : Nat  -- east color
  w : Nat  -- west color
abbrev TileSet := List WangTile
abbrev TileIn (T : TileSet) := { t : WangTile // t ∈ T }
```

Colors are natural numbers. A tile is encoded by `(n, s, e, w)` using
`WangTile.equivTuple`; a tileset uses the list encoding. Tiles are translated,
without rotations or reflections. The checked expansion below gives the entire
plane-tiling predicate, including membership and both matching conditions.
-/

namespace Tiling.MainResults

/-- The exact Wang predicate used in the reduction statements, with its definitions expanded. -/
theorem wang_tiling_definition (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔
      ∃ x : ℤ × ℤ → {t : LeanWang.WangTile // t ∈ T},
        (∀ p : ℤ × ℤ, (x p).1.e = (x (p.1 + 1, p.2)).1.w) ∧
        (∀ p : ℤ × ℤ, (x p).1.n = (x (p.1, p.2 + 1)).1.s) := Iff.rfl

end Tiling.MainResults
