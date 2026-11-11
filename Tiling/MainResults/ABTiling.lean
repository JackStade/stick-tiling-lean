import LeanWang.Basic

/-!
# AB tiling definitions

Tiles have width one and height two. A tiles start at even/even coordinates; B tiles
start at odd/odd coordinates. The four matching fields specify each vertical unit edge.
The two input lists may have different lengths or be empty.
The Wang-to-AB construction and its proofs are in `Tiling/Proofs/ABTiling.lean`.
-/

namespace Tiling.AB

open LeanWang

/-! ## AB tiles -/

/-- A `1 × 2` AB tile: `ul`, `ur`, `ll`, `lr` are the colors of the upper-left, upper-right,
lower-left and lower-right unit edges of the tile (the left and right long edges are each split
into an upper and a lower unit segment). -/
structure ABTile where
  ul : ℕ
  ur : ℕ
  ll : ℕ
  lr : ℕ
deriving DecidableEq, Repr

/-- View an AB tile as the quadruple of its edge colors. -/
def ABTile.toTuple (t : ABTile) : ℕ × ℕ × ℕ × ℕ :=
  (t.ul, t.ur, t.ll, t.lr)

/-- Build an AB tile from the quadruple of its edge colors. -/
def ABTile.ofTuple (p : ℕ × ℕ × ℕ × ℕ) : ABTile where
  ul := p.1
  ur := p.2.1
  ll := p.2.2.1
  lr := p.2.2.2

/-- AB tiles are encoded by their four natural-number edge colors. -/
def ABTile.equivTuple : ABTile ≃ ℕ × ℕ × ℕ × ℕ where
  toFun := ABTile.toTuple
  invFun := ABTile.ofTuple
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b, c, d⟩
    rfl

instance instPrimcodableABTile : Primcodable ABTile :=
  Primcodable.ofEquiv (ℕ × ℕ × ℕ × ℕ) ABTile.equivTuple

/-- An instance of the AB tiling problem: the finite set `A` of tiles allowed at even positions
and the finite set `B` of tiles allowed at odd positions, both given as lists. -/
structure ABTileSet where
  A : List ABTile
  B : List ABTile
deriving DecidableEq, Repr

/-- An AB tileset is the pair of its two lists of tiles. -/
def ABTileSet.equivProd : ABTileSet ≃ List ABTile × List ABTile where
  toFun S := (S.A, S.B)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro S
    cases S
    rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b⟩
    rfl

instance instPrimcodableABTileSet : Primcodable ABTileSet :=
  Primcodable.ofEquiv (List ABTile × List ABTile) ABTileSet.equivProd

/-! ## AB tilings of the plane -/

/-- The height of the lower-left corner of the tile `t x k` of an AB tiling: in an even column the
dominoes start at even heights, in an odd column at odd heights. -/
def tileHeight (x k : ℤ) : ℤ := if Even x then 2 * k else 2 * k + 1

/-- `t` is a valid AB tiling for the tileset `S`.  Here `t x k` is the tile placed in column `x`
with its lower-left corner at height `tileHeight x k`. -/
structure ValidABTiling (S : ABTileSet) (t : ℤ → ℤ → ABTile) : Prop where
  /-- Tiles in even columns come from `A`. -/
  memA : ∀ x k : ℤ, Even x → t x k ∈ S.A
  /-- Tiles in odd columns come from `B`. -/
  memB : ∀ x k : ℤ, ¬ Even x → t x k ∈ S.B
  /-- For even `x`, along the unit edge at height `2 * k + 1` between columns `x` and `x + 1`. -/
  matchEvenLow : ∀ x k : ℤ, Even x → (t x k).ur = (t (x + 1) k).ll
  /-- For even `x`, along the unit edge at height `2 * k + 2` between columns `x` and `x + 1`. -/
  matchEvenHigh : ∀ x k : ℤ, Even x → (t x (k + 1)).lr = (t (x + 1) k).ul
  /-- For odd `x`, along the unit edge at height `2 * k + 1` between columns `x` and `x + 1`. -/
  matchOddLow : ∀ x k : ℤ, ¬ Even x → (t x k).lr = (t (x + 1) k).ul
  /-- For odd `x`, along the unit edge at height `2 * k + 2` between columns `x` and `x + 1`. -/
  matchOddHigh : ∀ x k : ℤ, ¬ Even x → (t x k).ur = (t (x + 1) (k + 1)).ll

/-- An AB tileset admits a tiling of the plane. -/
def ABTilesPlane (S : ABTileSet) : Prop :=
  ∃ t : ℤ → ℤ → ABTile, ValidABTiling S t

end Tiling.AB
