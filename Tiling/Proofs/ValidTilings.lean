import Tiling.Proofs.MatchingRules

/-!
# First consequences of the matching rules

This file records some basic consequences of the definitions of
`Tiling/Proofs/MatchingRules.lean`.

The main one, `StickTiling.dir_ne_of_idx_eq_one`, is the first step of the proof of Lemma 4 of
the paper: in a valid tiling the stick that meets the head end (respectively the tail end) of a
stick — the ends carrying the labels `y₁` and `y₂` — is never parallel to it, since two parallel
sticks would necessarily match a `y` label with a `y` label, which rule 1 forbids.

As a sanity check we also show that the matching rules are restrictive: the tiling `rows` by
horizontal sticks laid end to end is not valid.
-/

namespace StickPolyhex

namespace StickTiling

variable {n : ℕ} (T : StickTiling n)

/-- The edge of a cell facing the head of its stick carries the label `y₁` when the cell is the
head, and is interior to the stick otherwise. -/
@[simp] lemma label_opp_dir (c : Hex) :
    T.label c (T.dir c).opp = if T.idx c = 1 then some .y1 else none := by
  have h : (T.dir c).opp - T.dir c + HexDir.W = HexDir.E := (sub_add_W_eq_E_iff _ _).2 rfl
  rw [label, h, frameLabel_E]

/-- The edge of a cell facing the tail of its stick carries the label `y₂` when the cell is the
tail, and is interior to the stick otherwise. -/
@[simp] lemma label_dir (c : Hex) :
    T.label c (T.dir c) = if T.idx c = n then some .y2 else none := by
  have h : T.dir c - T.dir c + HexDir.W = HexDir.W := (sub_add_W_eq_W_iff _ _).2 rfl
  rw [label, h, frameLabel_W]

/-- In a valid tiling, the stick meeting the head end of a stick is not parallel to it. -/
theorem dir_ne_of_idx_eq_one (hv : T.SatisfiesWeaveRules) {c : Hex} (h1 : T.idx c = 1) :
    T.dir (nbr c (T.dir c).opp) ≠ T.dir c ∧
      T.dir (nbr c (T.dir c).opp) ≠ (T.dir c).opp := by
  set c' : Hex := nbr c (T.dir c).opp with hc'
  have hlab : T.label c (T.dir c).opp = some .y1 := by simp [h1]
  have hne : T.label c' (T.dir c) ≠ none := by
    have h := (T.label_eq_none_comm c (T.dir c).opp).not
    simp only [HexDir.opp_opp] at h
    rw [← hc'] at h
    intro hnone
    exact (h.mp (by rw [hlab]; exact Option.some_ne_none _)) hnone
  have key : ∀ q : StickEdge, T.label c' (T.dir c) = some q → ¬ Forbidden n .y1 q :=
    fun q hq => hv c (T.dir c).opp .y1 q hlab (by simpa using hq)
  constructor
  · intro hd
    have hlab' : T.label c' (T.dir c) = if T.idx c' = n then some .y2 else none := by
      rw [← hd]; exact T.label_dir c'
    by_cases hidx : T.idx c' = n
    · rw [hidx, if_pos rfl] at hlab'
      exact key .y2 hlab' (Or.inl (ForbiddenCore.rule1 (Or.inl rfl) (Or.inr rfl)))
    · rw [if_neg hidx] at hlab'
      exact hne hlab'
  · intro hd
    have hd' : T.dir c = (T.dir c').opp := by rw [hd, HexDir.opp_opp]
    have hlab' : T.label c' (T.dir c) = if T.idx c' = 1 then some .y1 else none := by
      rw [hd']; exact T.label_opp_dir c'
    by_cases hidx : T.idx c' = 1
    · rw [hidx, if_pos rfl] at hlab'
      exact key .y1 hlab' (Or.inl (ForbiddenCore.rule1 (Or.inl rfl) (Or.inl rfl)))
    · rw [if_neg hidx] at hlab'
      exact hne hlab'

/-- In a valid tiling, the stick meeting the tail end of a stick is not parallel to it. -/
theorem dir_ne_of_idx_eq_length (hv : T.SatisfiesWeaveRules) {c : Hex} (hn : T.idx c = n) :
    T.dir (nbr c (T.dir c)) ≠ T.dir c ∧ T.dir (nbr c (T.dir c)) ≠ (T.dir c).opp := by
  set c' : Hex := nbr c (T.dir c) with hc'
  have hlab : T.label c (T.dir c) = some .y2 := by simp [hn]
  have hne : T.label c' (T.dir c).opp ≠ none := by
    have h := (T.label_eq_none_comm c (T.dir c)).not
    rw [← hc'] at h
    intro hnone
    exact (h.mp (by rw [hlab]; exact Option.some_ne_none _)) hnone
  have key : ∀ q : StickEdge, T.label c' (T.dir c).opp = some q → ¬ Forbidden n .y2 q :=
    fun q hq => hv c (T.dir c) .y2 q hlab hq
  constructor
  · intro hd
    have hlab' : T.label c' (T.dir c).opp = if T.idx c' = 1 then some .y1 else none := by
      rw [← hd]; exact T.label_opp_dir c'
    by_cases hidx : T.idx c' = 1
    · rw [hidx, if_pos rfl] at hlab'
      exact key .y1 hlab' (Or.inl (ForbiddenCore.rule1 (Or.inr rfl) (Or.inl rfl)))
    · rw [if_neg hidx] at hlab'
      exact hne hlab'
  · intro hd
    have hd' : (T.dir c).opp = T.dir c' := by rw [hd]
    have hlab' : T.label c' (T.dir c).opp = if T.idx c' = n then some .y2 else none := by
      rw [hd']; exact T.label_dir c'
    by_cases hidx : T.idx c' = n
    · rw [hidx, if_pos rfl] at hlab'
      exact key .y2 hlab' (Or.inl (ForbiddenCore.rule1 (Or.inr rfl) (Or.inr rfl)))
    · rw [if_neg hidx] at hlab'
      exact hne hlab'

/-- The matching rules really are restrictive: the tiling of the plane by rows of horizontal
sticks laid end to end is not valid, because two sticks then meet along a `y` edge. -/
theorem not_satisfiesWeaveRules_rows (n : ℕ) (hn : 0 < n) : ¬ (rows n hn).SatisfiesWeaveRules := by
  intro hv
  have hidx : (rows n hn).idx ((0 : ℤ), (0 : ℤ)) = 1 := by
    simp [rows]
  exact ((rows n hn).dir_ne_of_idx_eq_one hv hidx).1 rfl

end StickTiling

end StickPolyhex
