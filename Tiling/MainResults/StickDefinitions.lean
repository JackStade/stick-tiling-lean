import Tiling.MainResults.HexGrid

/-!
# Stick tiling: definitions used in the main statements

Read in order: `StickTiling` (the geometry), `StickEdge` and `frameLabel` (the boundary),
`ForbiddenCore` (the eleven base rules), `EdgeRules` and `StickTiling.SatisfiesRules`
(the meaning of matching), then `Marking` and `markedRules` (the extra marks).
Only elementary well-formedness proofs needed to construct these objects are included here.
Geometric and reduction proofs live in the `Tiling.Proofs` modules.
-/

namespace StickPolyhex

/-- A tiling of the hexagonal grid by sticks of length `n`, recorded cell-by-cell.

For each cell `c` we record the orientation `dir c` of the stick covering `c` (the direction
along the stick in which the index increases) and the index `idx c ∈ {1, …, n}` of `c` inside
that stick.  The remaining fields are the local consistency rules which guarantee that this
labelling comes from an actual tiling by sticks of length `n`. -/
structure StickTiling (n : ℕ) where
  /-- The orientation of the stick covering a cell: the direction along the stick in which the
  index increases. -/
  dir : Hex → HexDir
  /-- The index of a cell inside the stick covering it, a number in `{1, …, n}`. -/
  idx : Hex → ℕ
  /-- Indices are at least `1`. -/
  idx_pos : ∀ c, 1 ≤ idx c
  /-- Indices are at most `n`. -/
  idx_le : ∀ c, idx c ≤ n
  /-- A cell which is not the last cell of its stick is followed, in the direction of the stick,
  by a cell of the same stick. -/
  succ_dir : ∀ c, idx c < n → dir (nbr c (dir c)) = dir c
  /-- The index increases by one along the direction of the stick. -/
  succ_idx : ∀ c, idx c < n → idx (nbr c (dir c)) = idx c + 1
  /-- A cell which is not the first cell of its stick is preceded, in the direction of the stick,
  by a cell of the same stick. -/
  pred_dir : ∀ c, 1 < idx c → dir (nbr c (dir c).opp) = dir c
  /-- The index decreases by one against the direction of the stick. -/
  pred_idx : ∀ c, 1 < idx c → idx (nbr c (dir c).opp) = idx c - 1

/-- The labels on the boundary edges of the stick prototile. -/
inductive StickEdge : Type
  /-- The lower-right edge of the head hexagon. -/
  | x1 : StickEdge
  /-- The upper-left edge of the tail hexagon. -/
  | x2 : StickEdge
  /-- The right vertical edge of the head hexagon. -/
  | y1 : StickEdge
  /-- The left vertical edge of the tail hexagon. -/
  | y2 : StickEdge
  /-- The upper-right edge of the head hexagon. -/
  | z1 : StickEdge
  /-- The lower-left edge of the tail hexagon. -/
  | z2 : StickEdge
  /-- `a i`, `1 ≤ i ≤ n-1`: the upper-left edge of the hexagon with index `i`. -/
  | a : ℕ → StickEdge
  /-- `b i`, `1 ≤ i ≤ n-1`: the upper-right edge of the hexagon with index `i + 1`. -/
  | b : ℕ → StickEdge
  /-- `c i`, `1 ≤ i ≤ n-1`: the lower-right edge of the hexagon with index `n + 1 - i`. -/
  | c : ℕ → StickEdge
  /-- `d i`, `1 ≤ i ≤ n-1`: the lower-left edge of the hexagon with index `n - i`. -/
  | d : ℕ → StickEdge
  deriving DecidableEq, Repr

/-- The label carried, in the reference frame of the prototile, by the edge in direction `f` of
the hexagon with index `i` of a stick of length `n`.  The value `none` means that the edge is
interior to the stick, i.e. shared with the previous or the next hexagon of the same stick. -/
def frameLabel (n i : ℕ) (f : HexDir) : Option StickEdge :=
  ![ -- east
     if i = 1 then some .y1 else none,
     -- north-east
     if i = 1 then some .z1 else some (.b (i - 1)),
     -- north-west
     if i = n then some .x2 else some (.a i),
     -- west
     if i = n then some .y2 else none,
     -- south-west
     if i = n then some .z2 else some (.d (n - i)),
     -- south-east
     if i = 1 then some .x1 else some (.c (n + 1 - i)) ] f

@[simp] lemma frameLabel_E (n i : ℕ) :
    frameLabel n i HexDir.E = if i = 1 then some .y1 else none := rfl

@[simp] lemma frameLabel_NE (n i : ℕ) :
    frameLabel n i HexDir.NE = if i = 1 then some .z1 else some (.b (i - 1)) := rfl

@[simp] lemma frameLabel_NW (n i : ℕ) :
    frameLabel n i HexDir.NW = if i = n then some .x2 else some (.a i) := rfl

@[simp] lemma frameLabel_W (n i : ℕ) :
    frameLabel n i HexDir.W = if i = n then some .y2 else none := rfl

@[simp] lemma frameLabel_SW (n i : ℕ) :
    frameLabel n i HexDir.SW = if i = n then some .z2 else some (.d (n - i)) := rfl

@[simp] lemma frameLabel_SE (n i : ℕ) :
    frameLabel n i HexDir.SE = if i = 1 then some .x1 else some (.c (n + 1 - i)) := rfl

/-- An edge of a hexagon of a stick is interior to the stick exactly when it is the east edge of
a non-head hexagon or the west edge of a non-tail hexagon. -/
lemma frameLabel_eq_none_iff (n i : ℕ) (f : HexDir) :
    frameLabel n i f = none ↔ (f = HexDir.E ∧ i ≠ 1) ∨ (f = HexDir.W ∧ i ≠ n) := by
  rcases HexDir.cases_six f with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · by_cases h1 : i = 1 <;> by_cases h2 : i = n <;> simp [h1, h2] <;>
        split_ifs <;> simp

/-- The pairs of edge labels that the matching rules of the paper forbid from meeting, listed as
in rules 1–11 of the paper (`n` is the length of the stick).  The relation `Forbidden` below is
the symmetric closure of this relation. -/
inductive ForbiddenCore (n : ℕ) : StickEdge → StickEdge → Prop
  /-- Rule 1: `(yᵢ, yⱼ)`. -/
  | rule1 {p q : StickEdge} (hp : p = .y1 ∨ p = .y2) (hq : q = .y1 ∨ q = .y2) : ForbiddenCore n p q
  /-- Rule 2: `(xᵢ, xⱼ)`. -/
  | rule2x {p q : StickEdge} (hp : p = .x1 ∨ p = .x2) (hq : q = .x1 ∨ q = .x2) :
      ForbiddenCore n p q
  /-- Rule 2: `(zᵢ, zⱼ)`. -/
  | rule2z {p q : StickEdge} (hp : p = .z1 ∨ p = .z2) (hq : q = .z1 ∨ q = .z2) :
      ForbiddenCore n p q
  /-- Rule 3: `(yᵢ, xⱼ)`. -/
  | rule3 {p q : StickEdge} (hp : p = .y1 ∨ p = .y2) (hq : q = .x1 ∨ q = .x2) : ForbiddenCore n p q
  /-- Rule 4: `(xᵢ, zⱼ)`. -/
  | rule4 {p q : StickEdge} (hp : p = .x1 ∨ p = .x2) (hq : q = .z1 ∨ q = .z2) : ForbiddenCore n p q
  /-- Rule 5: `(yᵢ, a₁)` and `(yᵢ, c₁)`. -/
  | rule5 {p q : StickEdge} (hp : p = .y1 ∨ p = .y2) (hq : q = .a 1 ∨ q = .c 1) :
      ForbiddenCore n p q
  /-- Rule 6: `(x₁, cᵢ)` for `1 ≤ i ≤ n-1`. -/
  | rule6 {i : ℕ} (hi : 1 ≤ i) (hi' : i ≤ n - 1) : ForbiddenCore n .x1 (.c i)
  /-- Rule 7: `(z₂, dᵢ)` for `1 ≤ i ≤ n-2`. -/
  | rule7 {i : ℕ} (hi : 1 ≤ i) (hi' : i ≤ n - 2) : ForbiddenCore n .z2 (.d i)
  /-- Rule 8: `(x₂, aᵢ)` for `1 ≤ i ≤ n-1`. -/
  | rule8 {i : ℕ} (hi : 1 ≤ i) (hi' : i ≤ n - 1) : ForbiddenCore n .x2 (.a i)
  /-- Rule 9: `(z₁, bᵢ)` for `1 ≤ i ≤ n-1`. -/
  | rule9 {i : ℕ} (hi : 1 ≤ i) (hi' : i ≤ n - 1) : ForbiddenCore n .z1 (.b i)
  /-- Rule 10: `(yᵢ, z₂)`. -/
  | rule10 {p : StickEdge} (hp : p = .y1 ∨ p = .y2) : ForbiddenCore n p .z2
  /-- Rule 11: `(yᵢ, d_{n-1})`. -/
  | rule11 {p : StickEdge} (hp : p = .y1 ∨ p = .y2) : ForbiddenCore n p (.d (n - 1))

/-- Two edge labels may not be matched with each other. -/
def Forbidden (n : ℕ) (p q : StickEdge) : Prop := ForbiddenCore n p q ∨ ForbiddenCore n q p

lemma Forbidden.symm {n : ℕ} {p q : StickEdge} (h : Forbidden n p q) : Forbidden n q p :=
  Or.symm h

/-- An arbitrary set of edge-to-edge matching rules for the stick prototile of length `n`.

The prototile is drawn in the reference frame of `Tiling/Proofs/MatchingRules.lean`: the arrow
points down and the hexagons are numbered `1, …, n` from right to left, so the index increases
in the direction `HexDir.W`.  The field `frameLabel i f` gives the label carried by the edge in
direction `f` of the hexagon with index `i`, the value `none` meaning that this edge is interior
to the stick, and `Forbidden p q` says that an edge labelled `p` may not be matched against an
edge labelled `q`. -/
structure EdgeRules (n : ℕ) where
  /-- The type of labels carried by the boundary edges of the prototile. -/
  Label : Type
  /-- The label carried, in the reference frame, by the edge in direction `f` of the hexagon
  with index `i`; `none` means that the edge is interior to the stick. -/
  frameLabel : ℕ → HexDir → Option Label
  /-- Exactly the edges interior to the stick are unlabelled. -/
  frameLabel_eq_none_iff : ∀ i f,
    frameLabel i f = none ↔ (f = HexDir.E ∧ i ≠ 1) ∨ (f = HexDir.W ∧ i ≠ n)
  /-- The pairs of labels that may not be matched against each other. -/
  Forbidden : Label → Label → Prop
  /-- The two edges of a matched pair play the same role, so the relation is symmetric. -/
  forbidden_symm : ∀ {p q : Label}, Forbidden p q → Forbidden q p

namespace StickTiling

variable {n : ℕ} (T : StickTiling n) (R : EdgeRules n)

/-- The label carried by the edge in direction `e` of the cell `c` of the tiling `T`, according
to the rule set `R` (`none` if the edge is interior to a stick).

As in `StickTiling.label`, the stick covering `c` is the reference stick rotated by the rotation
taking `HexDir.W`, the direction of increasing index in the reference picture, to the
orientation `T.dir c`. -/
def labelOf (c : Hex) (e : HexDir) : Option R.Label :=
  R.frameLabel (T.idx c) (e - T.dir c + HexDir.W)

/-- The tiling `T` *satisfies* the edge-matching rules `R` when no two matched edges of `T`
carry a pair of labels forbidden by `R`.

Together with the local consistency rules that are part of the `StickTiling` structure, this is
the notion of a tiling of the plane by the decorated stick prototile described by `R`. -/
def SatisfiesRules : Prop :=
  ∀ (c : Hex) (e : HexDir) (p q : R.Label),
    T.labelOf R c e = some p → T.labelOf R (nbr c e) e.opp = some q → ¬ R.Forbidden p q

end StickTiling

/-- The arrow and triangle marks drawn on a block of length `n`, recorded as the sets of the
*positions* (the points at distance `1 + i` from the left end of the block, `0 ≤ i ≤ n - 1`)
at which each kind of mark occurs. -/
structure Marking (n : ℕ) where
  /-- The positions of the left-facing arrow marks on the top face of the block. -/
  topArrowL : Set ℕ
  /-- The positions of the right-facing arrow marks on the top face of the block. -/
  topArrowR : Set ℕ
  /-- The positions of the left-facing arrow marks on the bottom face of the block. -/
  botArrowL : Set ℕ
  /-- The positions of the right-facing arrow marks on the bottom face of the block. -/
  botArrowR : Set ℕ
  /-- The positions of the left-facing triangle marks on the top face of the block. -/
  triangleL : Set ℕ
  /-- The positions of the right-facing triangle marks on the top face of the block. -/
  triangleR : Set ℕ

/-- The pairs of edge labels forbidden by the markings `M` of a block of length `n`, listed in
the order of the paper; `MarkForbidden` below is the symmetric closure of this relation. -/
inductive MarkForbiddenCore (n : ℕ) (M : Marking n) : StickEdge → StickEdge → Prop
  /-- A left-facing arrow mark on the top at position `i` forbids `(a_{n-i}, y₂)`. -/
  | topArrowL {i : ℕ} {p q : StickEdge} (hi : i < n) (hm : i ∈ M.topArrowL)
      (hp : p = .a (n - i)) (hq : q = .y2) : MarkForbiddenCore n M p q
  /-- A right-facing arrow mark on the top at position `i` forbids `(a_{n-i-1}, y₁)`. -/
  | topArrowR {i : ℕ} {p q : StickEdge} (hi : i < n) (hm : i ∈ M.topArrowR)
      (hp : p = .a (n - i - 1)) (hq : q = .y1) : MarkForbiddenCore n M p q
  /-- A left-facing arrow mark on the bottom at position `i` forbids `(c_{i+1}, y₁)`. -/
  | botArrowL {i : ℕ} {p q : StickEdge} (hi : i < n) (hm : i ∈ M.botArrowL)
      (hp : p = .c (i + 1)) (hq : q = .y1) : MarkForbiddenCore n M p q
  /-- A right-facing arrow mark on the bottom at position `i` forbids `(c_{i+2}, y₂)`. -/
  | botArrowR {i : ℕ} {p q : StickEdge} (hi : i < n) (hm : i ∈ M.botArrowR)
      (hp : p = .c (i + 2)) (hq : q = .y2) : MarkForbiddenCore n M p q
  /-- The pair `(a_{n-i}, x₁)` is forbidden unless a right-facing triangle faces position `i`. -/
  | triangleR {i : ℕ} {p q : StickEdge} (hi : i + 2 ≤ n) (hm : i ∉ M.triangleR)
      (hp : p = .a (n - i)) (hq : q = .x1) : MarkForbiddenCore n M p q
  /-- The pair `(b_{n-1-i}, z₂)` is forbidden unless a left-facing triangle faces position
  `i`. -/
  | triangleL {i : ℕ} {p q : StickEdge} (hi : i + 2 ≤ n) (hm : i ∉ M.triangleL)
      (hp : p = .b (n - 1 - i)) (hq : q = .z2) : MarkForbiddenCore n M p q

/-- Two edge labels that the markings `M` forbid from meeting. -/
def MarkForbidden (n : ℕ) (M : Marking n) (p q : StickEdge) : Prop :=
  MarkForbiddenCore n M p q ∨ MarkForbiddenCore n M q p

lemma MarkForbidden.symm {n : ℕ} {M : Marking n} {p q : StickEdge} (h : MarkForbidden n M p q) :
    MarkForbidden n M q p := Or.symm h

/-- The edge-matching rules of a stick of length `n + 1` decorated according to the markings `M`
of a block of length `n`: the eleven rules of the paper together with the pairs forbidden by the
arrow and triangle marks. -/
def markedRules (n : ℕ) (M : Marking n) : EdgeRules (n + 1) where
  Label := StickEdge
  frameLabel := frameLabel (n + 1)
  frameLabel_eq_none_iff := frameLabel_eq_none_iff (n + 1)
  Forbidden p q := Forbidden (n + 1) p q ∨ MarkForbidden n M p q
  forbidden_symm h := h.imp Forbidden.symm MarkForbidden.symm

end StickPolyhex
