import Mathlib.Computability.Primrec.List
import Tiling.MainResults.StickDefinitions

/-!
# Instances of the stick tiling problem

The decision problem studied in the paper is: *given a stick prototile carrying edge-to-edge
matching rules, does it tile the hexagonal grid?*  To speak about the computability of this
problem the instances have to be finite pieces of data.  This file records that data.

An instance is a `MarkData`: the length `blockLen` of a block (so that the stick has
`blockLen + 1` cells) together with six finite lists of positions, the positions of the arrow
marks on the top and the bottom face and of the two kinds of triangle marks, exactly the data of
a `Marking`.  A `MarkData` is a finite object: it is `Primcodable`, so it can be fed to a
Turing machine, and it determines the decorated prototile through `MarkData.toMarking` and the
rule set `markedRules`.

`StickTilesGrid d` is the corresponding decision problem: the sticks of length
`d.blockLen + 1` decorated by the marks of `d` tile the hexagonal grid subject to their
matching rules.
-/

namespace StickPolyhex

/-- A finite description of a marked stick prototile: the length of a block (the stick has one
more cell than that) and the six lists of positions carrying the arrow and triangle marks. -/
structure MarkData where
  /-- The length of a block; the stick prototile has `blockLen + 1` cells. -/
  blockLen : ℕ
  /-- The positions of the left-facing arrow marks on the top face. -/
  topArrowL : List ℕ
  /-- The positions of the right-facing arrow marks on the top face. -/
  topArrowR : List ℕ
  /-- The positions of the left-facing arrow marks on the bottom face. -/
  botArrowL : List ℕ
  /-- The positions of the right-facing arrow marks on the bottom face. -/
  botArrowR : List ℕ
  /-- The positions of the left-facing triangle marks on the top face. -/
  triangleL : List ℕ
  /-- The positions of the right-facing triangle marks on the top face. -/
  triangleR : List ℕ
deriving DecidableEq, Repr

namespace MarkData

/-- A `MarkData` is the tuple of its seven fields. -/
def equivTuple :
    MarkData ≃ ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ where
  toFun d := (d.blockLen, d.topArrowL, d.topArrowR, d.botArrowL, d.botArrowR, d.triangleL,
    d.triangleR)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
  left_inv := by intro d; cases d; rfl
  right_inv := by rintro ⟨a, b, c, e, f, g, h⟩; rfl

instance instPrimcodable : Primcodable MarkData :=
  Primcodable.ofEquiv _ equivTuple

/-- The marking described by a `MarkData`. -/
def toMarking (d : MarkData) : Marking d.blockLen where
  topArrowL := {p | p ∈ d.topArrowL}
  topArrowR := {p | p ∈ d.topArrowR}
  botArrowL := {p | p ∈ d.botArrowL}
  botArrowR := {p | p ∈ d.botArrowR}
  triangleL := {p | p ∈ d.triangleL}
  triangleR := {p | p ∈ d.triangleR}

/-- The edge-matching rules of the marked stick prototile described by a `MarkData`. -/
def rules (d : MarkData) : EdgeRules (d.blockLen + 1) :=
  markedRules d.blockLen d.toMarking

end MarkData

/-- **The grid stick tiling problem.**  The marked stick prototile described by `d` — a stick of
`d.blockLen + 1` cells carrying the arrow and triangle marks listed in `d`, i.e. the
corresponding edge-to-edge matching rules — admits a tiling of the hexagonal grid. -/
def StickTilesGrid (d : MarkData) : Prop :=
  ∃ T : StickTiling (d.blockLen + 1), T.SatisfiesRules d.rules

lemma stickTilesGrid_iff (d : MarkData) :
    StickTilesGrid d ↔
      ∃ T : StickTiling (d.blockLen + 1),
        T.SatisfiesRules (markedRules d.blockLen d.toMarking) := Iff.rfl

end StickPolyhex
