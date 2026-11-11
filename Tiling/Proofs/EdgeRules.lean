import Tiling.Proofs.MatchingRules

/-!
# Arbitrary edge-matching rules for stick tiles

`Tiling/Proofs/MatchingRules.lean` describes *one specific* decorated stick prototile: the one
of the paper, whose boundary labels are `x₁, x₂, y₁, y₂, z₁, z₂, aᵢ, bᵢ, cᵢ, dᵢ` and whose
matching rules are the eleven forbidden pairs of rules 1–11.  This file abstracts that data.

An `EdgeRules n` is an *arbitrary* set of edge-to-edge matching rules for a stick of length `n`:

* a type `Label` of edge labels;
* a labelling `frameLabel i f` of the edge in direction `f` of the hexagon with index `i` of the
  prototile, drawn in the reference frame (arrow pointing down, indices increasing towards `W`),
  where `none` records an edge interior to the stick;
* the well-formedness condition `frameLabel_eq_none_iff`, saying that the unlabelled edges are
  exactly the edges interior to the stick (the east edge of every hexagon but the head and the
  west edge of every hexagon but the tail);
* a relation `Forbidden` telling which pairs of labels may not be matched against each other,
  required to be symmetric, since the two edges of a matched pair play the same role.

A `StickTiling n` carries a labelling of all the edges of the grid induced by any such rule set
(`StickTiling.labelOf`), and it *satisfies* the rules when no two matched edges carry a
forbidden pair of labels (`StickTiling.SatisfiesRules`).

The rules of the paper are the instance `weaveRules n`, and satisfying them is precisely the
earlier notion of a valid tiling: `StickTiling.satisfiesWeaveRules_iff_satisfiesRules`.  At the other
extreme, `EdgeRules.unconstrained n` forbids nothing and is satisfied by every stick tiling.
-/

namespace StickPolyhex

namespace EdgeRules

/-- The rule set that forbids nothing: an undecorated stick of length `n`. -/
def unconstrained (n : ℕ) : EdgeRules n where
  Label := Unit
  frameLabel i f := if (f = HexDir.E ∧ i ≠ 1) ∨ (f = HexDir.W ∧ i ≠ n) then none else some ()
  frameLabel_eq_none_iff i f := by split_ifs with h <;> simp [h]
  Forbidden _ _ := False
  forbidden_symm h := h

end EdgeRules

namespace StickTiling

variable {n : ℕ} (T : StickTiling n) (R : EdgeRules n)

/-- An edge of the tiling is unlabelled exactly when it separates two cells of one stick. -/
lemma labelOf_eq_none_iff (c : Hex) (e : HexDir) :
    T.labelOf R c e = none ↔
      (e = (T.dir c).opp ∧ 1 < T.idx c) ∨ (e = T.dir c ∧ T.idx c < n) := by
  rw [labelOf, R.frameLabel_eq_none_iff]
  have hpos := T.idx_pos c
  have hle := T.idx_le c
  rw [sub_add_W_eq_E_iff, sub_add_W_eq_W_iff]
  constructor
  · rintro (⟨he, hi⟩ | ⟨he, hi⟩)
    · exact Or.inl ⟨he, by omega⟩
    · exact Or.inr ⟨he, by omega⟩
  · rintro (⟨he, hi⟩ | ⟨he, hi⟩)
    · exact Or.inl ⟨he, by omega⟩
    · exact Or.inr ⟨he, by omega⟩

/-- The labelling induced by any rule set is well matched: an edge is interior to a stick when
seen from one of its two sides if and only if it is interior when seen from the other side. -/
theorem labelOf_eq_none_comm (c : Hex) (e : HexDir) :
    T.labelOf R c e = none ↔ T.labelOf R (nbr c e) e.opp = none := by
  have key : ∀ (c : Hex) (e : HexDir), T.labelOf R c e = none →
      T.labelOf R (nbr c e) e.opp = none := by
    intro c e h
    rw [labelOf_eq_none_iff] at h
    rcases h with ⟨rfl, hi⟩ | ⟨rfl, hi⟩
    · have hd : T.dir (nbr c (T.dir c).opp) = T.dir c := T.pred_dir c hi
      have hidx : T.idx (nbr c (T.dir c).opp) = T.idx c - 1 := T.pred_idx c hi
      rw [labelOf_eq_none_iff, hd, hidx]
      have := T.idx_le c
      exact Or.inr ⟨by simp, by omega⟩
    · have hd : T.dir (nbr c (T.dir c)) = T.dir c := T.succ_dir c hi
      have hidx : T.idx (nbr c (T.dir c)) = T.idx c + 1 := T.succ_idx c hi
      rw [labelOf_eq_none_iff, hd, hidx]
      have := T.idx_pos c
      exact Or.inl ⟨rfl, by omega⟩
  refine ⟨key c e, fun h => ?_⟩
  have := key (nbr c e) e.opp h
  simpa using this

variable {T R}

/-- Matched labels may also not be forbidden in the reverse order; this is the symmetry of the
forbidden relation. -/
lemma not_forbidden_swap (h : T.SatisfiesRules R) {c : Hex} {e : HexDir} {p q : R.Label}
    (hp : T.labelOf R c e = some p) (hq : T.labelOf R (nbr c e) e.opp = some q) :
    ¬ R.Forbidden q p :=
  fun hf => h c e p q hp hq (R.forbidden_symm hf)

variable (T R)

/-- Every stick tiling satisfies the rule set that forbids nothing. -/
theorem satisfiesRules_unconstrained : T.SatisfiesRules (EdgeRules.unconstrained n) :=
  fun _ _ _ _ _ _ h => h

end StickTiling

/-- The rules of the paper, packaged as a set of edge-matching rules: the labels are the
boundary labels `x₁, x₂, y₁, y₂, z₁, z₂, aᵢ, bᵢ, cᵢ, dᵢ` of the stick prototile, laid out as in
`frameLabel`, and the forbidden pairs are the eleven families of rules 1–11. -/
def weaveRules (n : ℕ) : EdgeRules n where
  Label := StickEdge
  frameLabel := _root_.StickPolyhex.frameLabel n
  frameLabel_eq_none_iff := frameLabel_eq_none_iff n
  Forbidden := _root_.StickPolyhex.Forbidden n
  forbidden_symm h := h.symm

@[simp] lemma weaveRules_label (n : ℕ) : (weaveRules n).Label = StickEdge := rfl

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

@[simp] lemma labelOf_weaveRules (c : Hex) (e : HexDir) :
    T.labelOf (weaveRules n) c e = T.label c e := rfl

/-- A tiling satisfies the eleven matching rules of the paper exactly when it satisfies the
corresponding set of edge-matching rules. -/
theorem satisfiesWeaveRules_iff_satisfiesRules :
    T.SatisfiesWeaveRules ↔ T.SatisfiesRules (weaveRules n) := Iff.rfl

end StickTiling

end StickPolyhex
