import Tiling.Proofs.ABGapSpec
import Tiling.Proofs.ABTiling

/-!
# Index tilings: the combinatorial heart of an AB tiling

The construction of Sections 2.6–2.8 does not see the AB tiles themselves, only the *indices* of
the tiles used in each column, together with the four color-matching conditions.  This file
isolates that information.

An `IndexTiling D` records, for every column `c` and every band `n`, the index `ix c n` of the
tile used in the column `c` at the bottom of the band `n`, and the index `jx c n` of the tile
used in the same column halfway through the band.  Even columns carry `A` indices (numbers
`1, …, t`) and odd columns carry `B` indices (numbers `t+1, …, 2t`).  An `A` column does not
change its tile inside a band (`lockA`) while a `B` column does not change its tile between the
middle of a band and the middle of the next one (`lockB`); this is exactly the vertical offset of
half a tile between the `A` columns and the `B` columns of an AB tiling.  The four matching
conditions `match1, …, match4` are the four color matchings of an AB tiling, read through the
functions `h₁, …, h₄`.

`ABSim.abData` builds the data `ABData` of the construction out of a set of AB tiles: `t` is the
number of tiles of the larger of the two lists (indices are read modulo the length of the list,
so every index names a genuine tile), `K` is one more than the largest color, and `h₁, …, h₄`
read the four colors as described in `ABData`.  The main result,
`ABSim.nonempty_indexTiling_iff_abTilesPlane`, is that index tilings for that data are the same
thing as AB tilings of the given tile set.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB

/-- The combinatorial data of an AB tiling: the indices of the tiles used in every column, at the
bottom of a band (`ix`) and in the middle of a band (`jx`). -/
structure IndexTiling (D : ABData) where
  /-- The index of the tile of the column `c` at the bottom of the band `n`. -/
  ix : ℤ → ℤ → ℤ
  /-- The index of the tile of the column `c` in the middle of the band `n`. -/
  jx : ℤ → ℤ → ℤ
  /-- Every index names a tile. -/
  ix_mem : ∀ c n, 1 ≤ ix c n ∧ ix c n ≤ 2 * D.tz
  /-- Even columns carry `A` tiles. -/
  ix_even : ∀ c n, Even c → ix c n ≤ D.tz
  /-- Odd columns carry `B` tiles. -/
  ix_odd : ∀ c n, ¬ Even c → D.tz < ix c n
  /-- An `A` column keeps its tile inside a band. -/
  lockA : ∀ c n, Even c → jx c n = ix c n
  /-- A `B` column keeps its tile from the middle of a band to the middle of the next one. -/
  lockB : ∀ c n, ¬ Even c → jx c n = ix c (n + 1)
  /-- The first color matching, across a boundary from an `A` column to a `B` column. -/
  match1 : ∀ c n, Even c → D.h₁ (ix c n) = D.h₁ (ix (c + 1) n)
  /-- The second color matching, across a boundary from a `B` column to an `A` column. -/
  match2 : ∀ c n, ¬ Even c → D.h₂ (ix c n) = D.h₂ (ix (c + 1) n)
  /-- The third color matching, across a boundary from an `A` column to a `B` column. -/
  match3 : ∀ c n, Even c → D.h₃ (jx c n) = D.h₃ (jx (c + 1) n)
  /-- The fourth color matching, across a boundary from a `B` column to an `A` column. -/
  match4 : ∀ c n, ¬ Even c → D.h₄ (jx c n) = D.h₄ (jx (c + 1) n)

namespace IndexTiling

variable {D : ABData} (T : IndexTiling D)

lemma jx_even {c n : ℤ} (h : Even c) : T.jx c n ≤ D.tz := by
  rw [T.lockA c n h]; exact T.ix_even c n h

lemma jx_odd {c n : ℤ} (h : ¬ Even c) : D.tz < T.jx c n := by
  rw [T.lockB c n h]; exact T.ix_odd c (n + 1) h

end IndexTiling

/-! ## The data extracted from a set of AB tiles -/

/-- The tile all of whose colors are `0`, used as a dummy value. -/
def dfltTile : ABTile := ⟨0, 0, 0, 0⟩

/-- The largest color occurring on a list of tiles. -/
def maxColor : List ABTile → ℕ
  | [] => 0
  | u :: l => max (max u.ul u.ur) (max (max u.ll u.lr) (maxColor l))

lemma le_maxColor {l : List ABTile} {u : ABTile} (h : u ∈ l) :
    u.ul ≤ maxColor l ∧ u.ur ≤ maxColor l ∧ u.ll ≤ maxColor l ∧ u.lr ≤ maxColor l := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · simp only [maxColor]; omega
    · have := ih h'; simp only [maxColor]; omega

lemma dfltTile_le (l : List ABTile) :
    dfltTile.ul ≤ maxColor l ∧ dfltTile.ur ≤ maxColor l ∧ dfltTile.ll ≤ maxColor l ∧
      dfltTile.lr ≤ maxColor l := by
  simp [dfltTile]

lemma getD_mem_or (l : List ABTile) (i : ℕ) :
    l.getD i dfltTile ∈ l ∨ l.getD i dfltTile = dfltTile := by
  by_cases h : i < l.length
  · exact Or.inl (by rw [List.getD_eq_getElem l dfltTile h]; exact List.getElem_mem h)
  · exact Or.inr (List.getD_eq_default l dfltTile (by omega))

lemma getD_color_le (l l' : List ABTile) (i : ℕ) (hl : ∀ u ∈ l, u ∈ l') :
    (l.getD i dfltTile).ul ≤ maxColor l' ∧ (l.getD i dfltTile).ur ≤ maxColor l' ∧
      (l.getD i dfltTile).ll ≤ maxColor l' ∧ (l.getD i dfltTile).lr ≤ maxColor l' := by
  rcases getD_mem_or l i with h | h
  · exact le_maxColor (hl _ h)
  · rw [h]; exact dfltTile_le l'

/-- The number of tiles of each kind used by the construction: the length of the longer of the
two lists.  Indices are read modulo the length of the list they name a tile of, so that every
index does name a tile. -/
def tcount (S : ABTileSet) : ℕ := max S.A.length S.B.length

/-- The `A` tile named by the index `ℓ`. -/
def tileA (S : ABTileSet) (ℓ : ℤ) : ABTile :=
  S.A.getD (((ℓ - 1) % (S.A.length : ℤ)).toNat) dfltTile

/-- The `B` tile named by the index `ℓ`. -/
def tileB (S : ABTileSet) (ℓ : ℤ) : ABTile :=
  S.B.getD (((ℓ - 1 - (tcount S : ℤ)) % (S.B.length : ℤ)).toNat) dfltTile

lemma tileA_mem {S : ABTileSet} (hA : S.A ≠ []) (ℓ : ℤ) : tileA S ℓ ∈ S.A := by
  have hlen : 0 < S.A.length := List.length_pos_iff.2 hA
  have h1 : 0 ≤ (ℓ - 1) % (S.A.length : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hlen.ne')
  have h2 : (ℓ - 1) % (S.A.length : ℤ) < (S.A.length : ℤ) :=
    Int.emod_lt_of_pos _ (by exact_mod_cast hlen)
  have h3 : ((ℓ - 1) % (S.A.length : ℤ)).toNat < S.A.length := by omega
  rw [tileA, List.getD_eq_getElem S.A dfltTile h3]
  exact List.getElem_mem h3

lemma tileB_mem {S : ABTileSet} (hB : S.B ≠ []) (ℓ : ℤ) : tileB S ℓ ∈ S.B := by
  have hlen : 0 < S.B.length := List.length_pos_iff.2 hB
  have h1 : 0 ≤ (ℓ - 1 - (tcount S : ℤ)) % (S.B.length : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hlen.ne')
  have h2 : (ℓ - 1 - (tcount S : ℤ)) % (S.B.length : ℤ) < (S.B.length : ℤ) :=
    Int.emod_lt_of_pos _ (by exact_mod_cast hlen)
  have h3 : ((ℓ - 1 - (tcount S : ℤ)) % (S.B.length : ℤ)).toNat < S.B.length := by omega
  rw [tileB, List.getD_eq_getElem S.B dfltTile h3]
  exact List.getElem_mem h3

/-- The index naming a given `A` tile. -/
lemma tileA_index {S : ABTileSet} {u : ABTile} (h : u ∈ S.A) :
    ∃ ℓ : ℤ, 1 ≤ ℓ ∧ ℓ ≤ (tcount S : ℤ) ∧ tileA S ℓ = u := by
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem h
  refine ⟨(i : ℤ) + 1, by omega, by simp only [tcount]; omega, ?_⟩
  have hmod : ((i : ℤ) + 1 - 1) % (S.A.length : ℤ) = (i : ℤ) := by
    simp only [add_sub_cancel_right]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hi)
  rw [tileA, hmod, Int.toNat_natCast, List.getD_eq_getElem S.A dfltTile hi, hiu]

/-- The index naming a given `B` tile. -/
lemma tileB_index {S : ABTileSet} {u : ABTile} (h : u ∈ S.B) :
    ∃ ℓ : ℤ, (tcount S : ℤ) + 1 ≤ ℓ ∧ ℓ ≤ 2 * (tcount S : ℤ) ∧ tileB S ℓ = u := by
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem h
  have hle : S.B.length ≤ tcount S := by simp only [tcount]; omega
  refine ⟨(tcount S : ℤ) + (i : ℤ) + 1, by omega, by omega, ?_⟩
  have hmod : ((tcount S : ℤ) + (i : ℤ) + 1 - 1 - (tcount S : ℤ)) % (S.B.length : ℤ) = (i : ℤ) := by
    have : (tcount S : ℤ) + (i : ℤ) + 1 - 1 - (tcount S : ℤ) = (i : ℤ) := by ring
    rw [this]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hi)
  rw [tileB, hmod, Int.toNat_natCast, List.getD_eq_getElem S.B dfltTile hi, hiu]

/-- The number of colors used by the construction. -/
def kcount (S : ABTileSet) : ℕ := maxColor (S.A ++ S.B) + 1

lemma tileA_lt {S : ABTileSet} (ℓ : ℤ) :
    (tileA S ℓ).ul < kcount S ∧ (tileA S ℓ).ur < kcount S ∧ (tileA S ℓ).ll < kcount S ∧
      (tileA S ℓ).lr < kcount S := by
  have := getD_color_le S.A (S.A ++ S.B) (((ℓ - 1) % (S.A.length : ℤ)).toNat)
    (fun u hu => List.mem_append_left _ hu)
  simp only [kcount, tileA]
  omega

lemma tileB_lt {S : ABTileSet} (ℓ : ℤ) :
    (tileB S ℓ).ul < kcount S ∧ (tileB S ℓ).ur < kcount S ∧ (tileB S ℓ).ll < kcount S ∧
      (tileB S ℓ).lr < kcount S := by
  have := getD_color_le S.B (S.A ++ S.B) (((ℓ - 1 - (tcount S : ℤ)) % (S.B.length : ℤ)).toNat)
    (fun u hu => List.mem_append_right _ hu)
  simp only [kcount, tileB]
  omega

/-- The matching function reading the color `f` of an `A` tile and the color `g` of a `B` tile. -/
def hcolor (S : ABTileSet) (f g : ABTile → ℕ) (ℓ : ℤ) : ℤ :=
  if ℓ ≤ (tcount S : ℤ) then ((f (tileA S ℓ) : ℕ) : ℤ) else ((g (tileB S ℓ) : ℕ) : ℤ)

lemma hcolor_mem (S : ABTileSet) {f g : ABTile → ℕ}
    (hf : ∀ u : ABTile, f u = u.ul ∨ f u = u.ur ∨ f u = u.ll ∨ f u = u.lr)
    (hg : ∀ u : ABTile, g u = u.ul ∨ g u = u.ur ∨ g u = u.ll ∨ g u = u.lr) (ℓ : ℤ) :
    0 ≤ hcolor S f g ℓ ∧ hcolor S f g ℓ < (kcount S : ℤ) := by
  unfold hcolor
  split
  · have h1 := tileA_lt (S := S) ℓ
    have h2 := hf (tileA S ℓ)
    refine ⟨by positivity, ?_⟩
    have : f (tileA S ℓ) < kcount S := by rcases h2 with h | h | h | h <;> rw [h] <;> omega
    exact_mod_cast this
  · have h1 := tileB_lt (S := S) ℓ
    have h2 := hg (tileB S ℓ)
    refine ⟨by positivity, ?_⟩
    have : g (tileB S ℓ) < kcount S := by rcases h2 with h | h | h | h <;> rw [h] <;> omega
    exact_mod_cast this

/-- The data of the construction attached to a set of AB tiles. -/
def abData (S : ABTileSet) (hA : S.A ≠ []) : ABData where
  t := tcount S
  K := kcount S
  ht := by
    have : 0 < S.A.length := List.length_pos_iff.2 hA
    simp only [tcount]; omega
  hK := by simp only [kcount]; omega
  h₁ := hcolor S ABTile.ur ABTile.ll
  h₂ := hcolor S ABTile.ul ABTile.lr
  h₃ := hcolor S ABTile.lr ABTile.ul
  h₄ := hcolor S ABTile.ll ABTile.ur
  h₁_mem := hcolor_mem S (fun _ => Or.inr (Or.inl rfl)) (fun _ => Or.inr (Or.inr (Or.inl rfl)))
  h₂_mem := hcolor_mem S (fun _ => Or.inl rfl) (fun _ => Or.inr (Or.inr (Or.inr rfl)))
  h₃_mem := hcolor_mem S (fun _ => Or.inr (Or.inr (Or.inr rfl))) (fun _ => Or.inl rfl)
  h₄_mem := hcolor_mem S (fun _ => Or.inr (Or.inr (Or.inl rfl))) (fun _ => Or.inr (Or.inl rfl))

@[simp] lemma abData_tz (S : ABTileSet) (hA : S.A ≠ []) :
    (abData S hA).tz = (tcount S : ℤ) := rfl

@[simp] lemma abData_h₁ (S : ABTileSet) (hA : S.A ≠ []) :
    (abData S hA).h₁ = hcolor S ABTile.ur ABTile.ll := rfl

@[simp] lemma abData_h₂ (S : ABTileSet) (hA : S.A ≠ []) :
    (abData S hA).h₂ = hcolor S ABTile.ul ABTile.lr := rfl

@[simp] lemma abData_h₃ (S : ABTileSet) (hA : S.A ≠ []) :
    (abData S hA).h₃ = hcolor S ABTile.lr ABTile.ul := rfl

@[simp] lemma abData_h₄ (S : ABTileSet) (hA : S.A ≠ []) :
    (abData S hA).h₄ = hcolor S ABTile.ll ABTile.ur := rfl

/-! ## Index tilings are AB tilings -/

section

variable {S : ABTileSet} (hA : S.A ≠ [])

/-- The tile of an AB tiling read off from an index tiling. -/
def tileOfIndex (T : IndexTiling (abData S hA)) (x k : ℤ) : ABTile :=
  if Even x then tileA S (T.ix x (-k)) else tileB S (T.jx x (-k - 1))

lemma abTiling_of_indexTiling (hB : S.B ≠ []) (T : IndexTiling (abData S hA)) :
    ValidABTiling S (tileOfIndex hA T) := by
  have hcolA : ∀ (f g : ABTile → ℕ) (ℓ : ℤ), ℓ ≤ (tcount S : ℤ) →
      hcolor S f g ℓ = ((f (tileA S ℓ) : ℕ) : ℤ) := by
    intro f g ℓ h; rw [hcolor, if_pos h]
  have hcolB : ∀ (f g : ABTile → ℕ) (ℓ : ℤ), (tcount S : ℤ) < ℓ →
      hcolor S f g ℓ = ((g (tileB S ℓ) : ℕ) : ℤ) := by
    intro f g ℓ h; rw [hcolor, if_neg (by omega)]
  constructor
  · intro x k hx
    simp only [tileOfIndex, if_pos hx]
    exact tileA_mem hA _
  · intro x k hx
    simp only [tileOfIndex, if_neg hx]
    exact tileB_mem hB _
  · -- matchEvenLow
    intro x k hx
    have hx1 : ¬ Even (x + 1) := by simpa using hx.add_one
    have h := T.match1 x (-k) hx
    rw [abData_h₁] at h
    rw [hcolA _ _ _ (T.ix_even x (-k) hx), hcolB _ _ _ (T.ix_odd (x + 1) (-k) hx1)] at h
    have hj : T.jx (x + 1) (-k - 1) = T.ix (x + 1) (-k) := by
      rw [T.lockB (x + 1) (-k - 1) hx1]; ring_nf
    simp only [tileOfIndex, if_pos hx, if_neg hx1, hj]
    exact_mod_cast h
  · -- matchEvenHigh
    intro x k hx
    have hx1 : ¬ Even (x + 1) := by simpa using hx.add_one
    have h := T.match3 x (-k - 1) hx
    rw [abData_h₃] at h
    rw [hcolA _ _ _ (T.jx_even hx), hcolB _ _ _ (T.jx_odd hx1)] at h
    have hj : T.jx x (-k - 1) = T.ix x (-(k + 1)) := by
      rw [T.lockA x (-k - 1) hx]; ring_nf
    simp only [tileOfIndex, if_pos hx, if_neg hx1, ← hj]
    exact_mod_cast h
  · -- matchOddLow
    intro x k hx
    have hx1 : Even (x + 1) := by
      rcases Int.even_or_odd x with h | h
      · exact absurd h hx
      · obtain ⟨m, hm⟩ := h; exact ⟨m + 1, by omega⟩
    have h := T.match2 x (-k) hx
    rw [abData_h₂] at h
    rw [hcolB _ _ _ (T.ix_odd x (-k) hx), hcolA _ _ _ (T.ix_even (x + 1) (-k) hx1)] at h
    have hj : T.jx x (-k - 1) = T.ix x (-k) := by
      rw [T.lockB x (-k - 1) hx]; ring_nf
    simp only [tileOfIndex, if_neg hx, if_pos hx1, hj]
    exact_mod_cast h
  · -- matchOddHigh
    intro x k hx
    have hx1 : Even (x + 1) := by
      rcases Int.even_or_odd x with h | h
      · exact absurd h hx
      · obtain ⟨m, hm⟩ := h; exact ⟨m + 1, by omega⟩
    have h := T.match4 x (-k - 1) hx
    rw [abData_h₄] at h
    rw [hcolB _ _ _ (T.jx_odd hx), hcolA _ _ _ (T.jx_even hx1)] at h
    have hj : T.jx (x + 1) (-k - 1) = T.ix (x + 1) (-(k + 1)) := by
      rw [T.lockA (x + 1) (-k - 1) hx1]; ring_nf
    simp only [tileOfIndex, if_neg hx, if_pos hx1, ← hj]
    exact_mod_cast h

/-! ## AB tilings are index tilings -/

/-- The index of the tile of an AB tiling in the column `x` and the band `n`. -/
noncomputable def indexOfTile {t : ℤ → ℤ → ABTile} (ht : ValidABTiling S t) (x n : ℤ) : ℤ :=
  if hx : Even x then Classical.choose (tileA_index (ht.memA x (-n) hx))
  else Classical.choose (tileB_index (ht.memB x (-n) hx))

lemma indexOfTile_even {t : ℤ → ℤ → ABTile} (ht : ValidABTiling S t) {x : ℤ} (hx : Even x)
    (n : ℤ) :
    1 ≤ indexOfTile ht x n ∧ indexOfTile ht x n ≤ (tcount S : ℤ) ∧
      tileA S (indexOfTile ht x n) = t x (-n) := by
  have h := Classical.choose_spec (tileA_index (ht.memA x (-n) hx))
  simp only [indexOfTile, dif_pos hx]
  exact ⟨h.1, h.2.1, h.2.2⟩

lemma indexOfTile_odd {t : ℤ → ℤ → ABTile} (ht : ValidABTiling S t) {x : ℤ} (hx : ¬ Even x)
    (n : ℤ) :
    (tcount S : ℤ) + 1 ≤ indexOfTile ht x n ∧ indexOfTile ht x n ≤ 2 * (tcount S : ℤ) ∧
      tileB S (indexOfTile ht x n) = t x (-n) := by
  have h := Classical.choose_spec (tileB_index (ht.memB x (-n) hx))
  simp only [indexOfTile, dif_neg hx]
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The index tiling read off from an AB tiling. -/
noncomputable def indexTilingOfTiling {t : ℤ → ℤ → ABTile} (ht : ValidABTiling S t) :
    IndexTiling (abData S hA) where
  ix := fun c n => indexOfTile ht c n
  jx := fun c n => if Even c then indexOfTile ht c n else indexOfTile ht c (n + 1)
  ix_mem := by
    intro c n
    by_cases hc : Even c
    · have h := indexOfTile_even ht hc n
      have : (1 : ℤ) ≤ (tcount S : ℤ) := by
        have : 0 < S.A.length := List.length_pos_iff.2 hA
        simp only [tcount]; omega
      exact ⟨h.1, by simp only [abData_tz]; omega⟩
    · have h := indexOfTile_odd ht hc n
      exact ⟨by omega, by simp only [abData_tz]; omega⟩
  ix_even := by
    intro c n hc
    simp only [abData_tz]
    exact (indexOfTile_even ht hc n).2.1
  ix_odd := by
    intro c n hc
    simp only [abData_tz]
    have := (indexOfTile_odd ht hc n).1
    omega
  lockA := by intro c n hc; simp only [if_pos hc]
  lockB := by intro c n hc; simp only [if_neg hc]
  match1 := by
    intro c n hc
    have hc1 : ¬ Even (c + 1) := by simpa using hc.add_one
    have ha := indexOfTile_even ht hc n
    have hb := indexOfTile_odd ht hc1 n
    rw [abData_h₁, hcolor, if_pos ha.2.1, hcolor, if_neg (by omega), ha.2.2, hb.2.2]
    exact_mod_cast ht.matchEvenLow c (-n) hc
  match2 := by
    intro c n hc
    have hc1 : Even (c + 1) := by
      rcases Int.even_or_odd c with h | h
      · exact absurd h hc
      · obtain ⟨m, hm⟩ := h; exact ⟨m + 1, by omega⟩
    have ha := indexOfTile_odd ht hc n
    have hb := indexOfTile_even ht hc1 n
    rw [abData_h₂, hcolor, if_neg (by omega), hcolor, if_pos hb.2.1, ha.2.2, hb.2.2]
    exact_mod_cast ht.matchOddLow c (-n) hc
  match3 := by
    intro c n hc
    have hc1 : ¬ Even (c + 1) := by simpa using hc.add_one
    have ha := indexOfTile_even ht hc n
    have hb := indexOfTile_odd ht hc1 (n + 1)
    simp only [if_pos hc, if_neg hc1]
    rw [abData_h₃, hcolor, if_pos ha.2.1, hcolor, if_neg (by omega), ha.2.2, hb.2.2]
    have h := ht.matchEvenHigh c (-n - 1) hc
    have e1 : (-n - 1 + 1 : ℤ) = -n := by ring
    have e2 : (-(n + 1) : ℤ) = -n - 1 := by ring
    rw [e1] at h
    rw [e2]
    exact_mod_cast h
  match4 := by
    intro c n hc
    have hc1 : Even (c + 1) := by
      rcases Int.even_or_odd c with h | h
      · exact absurd h hc
      · obtain ⟨m, hm⟩ := h; exact ⟨m + 1, by omega⟩
    have ha := indexOfTile_odd ht hc (n + 1)
    have hb := indexOfTile_even ht hc1 n
    simp only [if_neg hc, if_pos hc1]
    rw [abData_h₄, hcolor, if_neg (by omega), hcolor, if_pos hb.2.1, ha.2.2, hb.2.2]
    have h := ht.matchOddHigh c (-n - 1) hc
    have e1 : (-n - 1 + 1 : ℤ) = -n := by ring
    have e2 : (-(n + 1) : ℤ) = -n - 1 := by ring
    rw [e1] at h
    rw [e2]
    exact_mod_cast h

/-- **The combinatorial reformulation of an AB tiling.**  A set of AB tiles admits a tiling of
the plane exactly when the data of the construction admits an index tiling. -/
theorem nonempty_indexTiling_iff_abTilesPlane (hB : S.B ≠ []) :
    Nonempty (IndexTiling (abData S hA)) ↔ ABTilesPlane S := by
  constructor
  · rintro ⟨T⟩
    exact ⟨_, abTiling_of_indexTiling hA hB T⟩
  · rintro ⟨t, ht⟩
    exact ⟨indexTilingOfTiling hA ht⟩

end

end ABSim

end StickPolyhex
