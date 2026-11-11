import Tiling.Proofs.GapAssignment

/-!
# Gap data read along the diagonal lines of the gap lattice

The data of a `GapAssignment` — a state for every row and a pair of values for every gap — can be
repackaged in a much more symmetric way, which is what the present file does and what all the
work of Sections 2.6–2.8 of the paper uses.

In a schematic the gaps form a diagonal lattice: the `k`-th gap of the row `r` has the gaps
`(r-1, k)` and `(r-1, k+1)` below it, to its left and to its right.  Its *left* value therefore
continues the right value of the gap above it to the left, and its *right* value continues the
left value of the gap above it to the right.  Following these chains one sees that the values
are organised in **lines**: the left value of the gap `(r, k)` and the right value of the gap
`(r - 1, k)` belong to the same line, and so do the right value of `(r, k)` and the left value of
`(r - 1, k + 1)`.  Labelling the line of the left value of the gap `(r, k)` by the integer
`J = 2 * k + r`, every line `J` carries exactly one value in every row `r`, namely

* the left value of the gap `(J - r) / 2` of the row `r`, when `J - r` is even,
* the right value of the gap `(J - r - 1) / 2` of the row `r`, when `J - r` is odd.

`LineAssignment G` records precisely this: a number `V J r` for every line `J` and row `r`, with
the paper's conditions expressed as

* `memL`/`memR`: the value on a line lies in `L` (resp. `R`) of the state of its row, according
  to the parity of `J - r`;
* `pair`: in the step from the row `r` to the row `r - 1`, two lines `J` (with `J - r` even) and
  `J + 1` — the two lines bounding one gap of the row `r` — change by opposite amounts;
* `intv`: the change of the line `J` (with `J - r` even) lies in the interval of the state of the
  row `r - 1`.

`LineAssignment.toGap` and `GapAssignment.toLine` translate between the two presentations.
-/

namespace StickPolyhex

/-- The data of a gap assignment, read along the diagonal lines of the gap lattice: `V J r` is
the value carried by the line `J` in the row `r`.  It is the left value of a gap of the row `r`
when `J - r` is even and the right value of a gap of the row `r` when `J - r` is odd. -/
structure LineAssignment (G : GapSpec) where
  /-- The state of a row. -/
  st : ℤ → ℕ
  /-- The value carried by the line `J` in the row `r`. -/
  V : ℤ → ℤ → ℤ
  /-- Every state is one of the `s` buckets. -/
  state_mem : ∀ r, 1 ≤ st r ∧ st r ≤ G.s
  /-- The row below a row of state `i` has state `σ i`. -/
  state_cycle : ∀ r, st (r - 1) = G.sigma (st r)
  /-- A line carrying a left value lies in `L` of the state of its row. -/
  memL : ∀ r J, (J - r) % 2 = 0 → V J r ∈ G.L (st r)
  /-- A line carrying a right value lies in `R` of the state of its row. -/
  memR : ∀ r J, (J - r) % 2 = 1 → V J r ∈ G.R (st r)
  /-- The two lines bounding a gap change by opposite amounts from one row to the next. -/
  pair : ∀ r J, (J - r) % 2 = 0 →
    V J (r - 1) - V J r = -(V (J + 1) (r - 1) - V (J + 1) r)
  /-- The change of a line carrying a left value lies in the interval of the row below. -/
  intv : ∀ r J, (J - r) % 2 = 0 →
    G.Imin (st (r - 1)) ≤ V J (r - 1) - V J r ∧ V J (r - 1) - V J r ≤ G.Imax (st (r - 1))

namespace LineAssignment

variable {G : GapSpec} (A : LineAssignment G)

/-! ### How the states run through the cycle -/

/-- One step down the rows advances the state by one, cyclically. -/
lemma st_step (r : ℤ) : A.st (r - 1) = if A.st r = G.s then 1 else A.st r + 1 := by
  rw [A.state_cycle r]; rfl

/-- The state `k` rows below a given row. -/
lemma st_add (r : ℤ) (k : ℕ) : A.st (r - k) = 1 + ((A.st r - 1 + k) % G.s) := by
  have hs := G.hs
  induction k with
  | zero =>
    have h1 := A.state_mem r
    have hmod : (A.st r - 1 + 0) % G.s = A.st r - 1 := Nat.mod_eq_of_lt (by omega)
    rw [show r - ((0 : ℕ) : ℤ) = r by push_cast; ring, hmod]
    omega
  | succ k ih =>
    have hcast : r - ((k + 1 : ℕ) : ℤ) = r - (k : ℤ) - 1 := by push_cast; ring
    have hstep := A.st_step (r - (k : ℤ))
    rw [ih] at hstep
    have hlt : (A.st r - 1 + k) % G.s < G.s := Nat.mod_lt _ (by omega)
    have hnext : (A.st r - 1 + (k + 1)) % G.s = ((A.st r - 1 + k) % G.s + 1) % G.s := by
      rw [← Nat.add_assoc]; exact (Nat.mod_add_mod _ _ _).symm
    have hval : ((A.st r - 1 + k) % G.s + 1) % G.s
        = if (A.st r - 1 + k) % G.s + 1 = G.s then 0 else (A.st r - 1 + k) % G.s + 1 := by
      by_cases hlast : (A.st r - 1 + k) % G.s + 1 = G.s
      · rw [if_pos hlast, hlast, Nat.mod_self]
      · rw [if_neg hlast, Nat.mod_eq_of_lt (by omega)]
    rw [hcast, hstep, hnext, hval]
    by_cases hlast : (A.st r - 1 + k) % G.s + 1 = G.s
    · rw [if_pos (by omega), if_pos hlast]
    · rw [if_neg (by omega), if_neg hlast]
      omega

/-- The states are periodic with period `s`. -/
lemma st_period (r : ℤ) : A.st (r - G.s) = A.st r := by
  have hs := G.hs
  have h1 := A.state_mem r
  have := A.st_add r G.s
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The states are periodic: going down any multiple of `s` rows leaves the state unchanged. -/
lemma st_period_int (r : ℤ) (k : ℤ) : A.st (r - (G.s : ℤ) * k) = A.st r := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have he : r - (G.s : ℤ) * (i + 1) = (r - (G.s : ℤ) * i) - G.s := by ring
    rw [he, A.st_period, ih]
  | pred i ih =>
    have he : r - (G.s : ℤ) * (-i) = (r - (G.s : ℤ) * (-i - 1)) - G.s := by ring
    rw [← ih, he, A.st_period]

/-- The gap assignment described by a line assignment. -/
def toGap : GapAssignment G where
  st := A.st
  xv := fun r k => A.V (2 * k + r) r
  yv := fun r k => A.V (2 * k + r + 1) r
  state_mem := A.state_mem
  state_cycle := A.state_cycle
  x_mem := fun r k => A.memL r (2 * k + r) (by omega)
  y_mem := fun r k => A.memR r (2 * k + r + 1) (by omega)
  value_sum := by
    intro r k
    have h := A.pair r (2 * k + r) (by omega)
    have e1 : 2 * k + (r - 1) + 1 = 2 * k + r := by ring
    have e2 : 2 * (k + 1) + (r - 1) = 2 * k + r + 1 := by ring
    rw [e1, e2]
    omega
  interval := by
    intro r k
    have h := A.intv r (2 * k + r) (by omega)
    have e1 : 2 * k + (r - 1) + 1 = 2 * k + r := by ring
    rw [e1]
    exact h

end LineAssignment

namespace GapAssignment

variable {G : GapSpec} (A : GapAssignment G)

/-- The line assignment describing a gap assignment. -/
noncomputable def toLine : LineAssignment G where
  st := A.st
  V := fun J r => if (J - r) % 2 = 0 then A.xv r ((J - r) / 2) else A.yv r ((J - r - 1) / 2)
  state_mem := A.state_mem
  state_cycle := A.state_cycle
  memL := by
    intro r J h
    simp only [if_pos h]
    exact A.x_mem r _
  memR := by
    intro r J h
    rw [if_neg (by omega)]
    exact A.y_mem r _
  pair := by
    intro r J h
    obtain ⟨k, hk⟩ : ∃ k : ℤ, J = 2 * k + r := ⟨(J - r) / 2, by omega⟩
    subst hk
    have h1 : (2 * k + r - (r - 1)) % 2 = 1 := by omega
    have h2 : (2 * k + r + 1 - (r - 1)) % 2 = 0 := by omega
    have h3 : (2 * k + r + 1 - r) % 2 = 1 := by omega
    rw [if_neg (by omega : ¬ (2 * k + r - (r - 1)) % 2 = 0),
      if_neg (by omega : ¬ (2 * k + r + 1 - r) % 2 = 0), if_pos h2, if_pos h]
    have e1 : (2 * k + r - (r - 1) - 1) / 2 = k := by omega
    have e2 : (2 * k + r + 1 - (r - 1)) / 2 = k + 1 := by omega
    have e3 : (2 * k + r + 1 - r - 1) / 2 = k := by omega
    have e4 : (2 * k + r - r) / 2 = k := by omega
    rw [e1, e2, e3, e4]
    have := A.value_sum r k
    omega
  intv := by
    intro r J h
    obtain ⟨k, hk⟩ : ∃ k : ℤ, J = 2 * k + r := ⟨(J - r) / 2, by omega⟩
    subst hk
    rw [if_neg (by omega : ¬ (2 * k + r - (r - 1)) % 2 = 0), if_pos h]
    have e1 : (2 * k + r - (r - 1) - 1) / 2 = k := by omega
    have e4 : (2 * k + r - r) / 2 = k := by omega
    rw [e1, e4]
    exact A.interval r k

end GapAssignment

/-- Gap assignments and line assignments are two presentations of the same data. -/
theorem nonempty_gapAssignment_iff_lineAssignment (G : GapSpec) :
    Nonempty (GapAssignment G) ↔ Nonempty (LineAssignment G) :=
  ⟨fun ⟨A⟩ => ⟨A.toLine⟩, fun ⟨A⟩ => ⟨A.toGap⟩⟩

end StickPolyhex
