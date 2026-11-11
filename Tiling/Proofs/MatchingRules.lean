import Tiling.Proofs.StickTiling

/-!
# Edge labels and the matching rules of the stick tile

The stick prototile of the paper carries labels on its boundary edges.  In the reference
picture the stick is drawn horizontally, with the arrow pointing down and the hexagons numbered
`1, …, n` from right to left, and the labels are, reading along the top from the right,
`z₁, a₁, b₁, a₂, b₂, …, a_{n-1}, b_{n-1}, x₂`, along the bottom from the left
`z₂, c₁, d₁, c₂, d₂, …, c_{n-1}, d_{n-1}, x₁`, and `y₁`, `y₂` on the right and left vertical
edges.  Hence, in the reference frame, the hexagon with index `i` carries

* on its east edge `y₁` if `i = 1` (otherwise the edge is interior to the stick),
* on its west edge `y₂` if `i = n` (otherwise the edge is interior),
* on its north-east edge `z₁` if `i = 1` and `b_{i-1}` otherwise,
* on its north-west edge `x₂` if `i = n` and `a_i` otherwise,
* on its south-east edge `x₁` if `i = 1` and `c_{n+1-i}` otherwise,
* on its south-west edge `z₂` if `i = n` and `d_{n-i}` otherwise.

Since the direction of increasing index is `W` in the reference frame, a cell of a
`StickTiling` whose orientation is `d` is obtained from the reference frame by the rotation
taking `W` to `d`; so the absolute direction `e` corresponds to the reference direction
`e - d + W`.  This is the content of `StickTiling.label`.

The edge-to-edge matching rules of the paper forbid eleven families of pairs of labels from
meeting; this is `Forbidden`.  A *valid* tiling is a `StickTiling` (i.e. a labelling satisfying
the local consistency rules of a tiling by sticks) all of whose adjacent pairs of labels are
allowed: `StickTiling.SatisfiesWeaveRules`.  This is exactly the hypothesis of Lemma 4 of the paper.
-/

namespace StickPolyhex

/-- The reference direction corresponding to the absolute direction `e` for a stick of
orientation `d` is `HexDir.E` exactly when `e` is opposite to `d`. -/
lemma sub_add_W_eq_E_iff (e d : HexDir) : e - d + HexDir.W = HexDir.E ↔ e = d.opp := by
  revert e d; decide

/-- The reference direction corresponding to the absolute direction `e` for a stick of
orientation `d` is `HexDir.W` exactly when `e = d`. -/
lemma sub_add_W_eq_W_iff (e d : HexDir) : e - d + HexDir.W = HexDir.W ↔ e = d := by
  revert e d; decide

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- The label carried by the edge in direction `e` of the cell `c` in the tiling `T`
(`none` if the edge is interior to a stick).

The stick covering `c` is the reference stick rotated by the rotation taking `W`, the direction
of increasing index in the reference picture, to the orientation `T.dir c`. -/
def label (c : Hex) (e : HexDir) : Option StickEdge :=
  frameLabel n (T.idx c) (e - T.dir c + HexDir.W)

lemma label_eq_none_iff (c : Hex) (e : HexDir) :
    T.label c e = none ↔ (e = (T.dir c).opp ∧ 1 < T.idx c) ∨ (e = T.dir c ∧ T.idx c < n) := by
  rw [label, frameLabel_eq_none_iff]
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

/-- An edge interior to a stick is interior seen from both of its sides. -/
lemma label_eq_none_of (c : Hex) (e : HexDir) (h : T.label c e = none) :
    T.label (nbr c e) e.opp = none := by
  rw [label_eq_none_iff] at h
  rcases h with ⟨rfl, hi⟩ | ⟨rfl, hi⟩
  · have hd : T.dir (nbr c (T.dir c).opp) = T.dir c := T.pred_dir c hi
    have hidx : T.idx (nbr c (T.dir c).opp) = T.idx c - 1 := T.pred_idx c hi
    rw [label_eq_none_iff, hd, hidx]
    have := T.idx_le c
    exact Or.inr ⟨by simp, by omega⟩
  · have hd : T.dir (nbr c (T.dir c)) = T.dir c := T.succ_dir c hi
    have hidx : T.idx (nbr c (T.dir c)) = T.idx c + 1 := T.succ_idx c hi
    rw [label_eq_none_iff, hd, hidx]
    have := T.idx_pos c
    exact Or.inl ⟨rfl, by omega⟩

/-- The labelling is well matched: an edge is interior to a stick when seen from one of its two
sides if and only if it is interior when seen from the other side. -/
theorem label_eq_none_comm (c : Hex) (e : HexDir) :
    T.label c e = none ↔ T.label (nbr c e) e.opp = none := by
  refine ⟨T.label_eq_none_of c e, fun h => ?_⟩
  have := T.label_eq_none_of (nbr c e) e.opp h
  simpa using this

end StickTiling

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- A stick tiling *satisfies the weave rules* when, besides being a genuine tiling by sticks of
length `n` (which is part of the `StickTiling` data), no two of its edges are matched in a way
forbidden by rules 1–11 of the paper. -/
def SatisfiesWeaveRules : Prop :=
  ∀ (c : Hex) (e : HexDir) (p q : StickEdge),
    T.label c e = some p → T.label (nbr c e) e.opp = some q → ¬ Forbidden n p q

end StickTiling

end StickPolyhex
