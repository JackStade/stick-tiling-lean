import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete
import Tiling.Proofs.EdgeRules
import Tiling.Proofs.StickInstance

/-!
# Compactness: tiling the grid is a local condition

A `StickTiling n` satisfying a set `R : EdgeRules n` of edge-to-edge matching rules is described
by purely *local* data: a label — an orientation together with an index in `{1, …, n}` — at
every cell of the hexagonal grid, subject to conditions relating each cell to its six
neighbours.  This file proves the corresponding compactness statement: the marked stick tiles
the whole grid as soon as *every finite set of cells* can be labelled consistently.

* `Labelling n` is the space of labellings, `Labelling.OKat R f c` the conjunction of all the
  conditions imposed at the cell `c`, and `Labelling.exists_stickTiling_iff` identifies globally
  consistent labellings with tilings satisfying the rules;
* `Labelling.exists_forall_okAt_of_finset` is the compactness argument: the space of labellings
  is a compact space, the conditions at a cell are closed, and a directed intersection of
  nonempty closed sets is nonempty;
* `stickTilesGrid_iff_forall_finset` states the result for the instances `MarkData` of the grid
  stick tiling problem: the marked stick tiles the hexagonal grid if and only if every finite
  set of cells carries a labelling satisfying all the conditions imposed at its cells;
* `stickTilesGrid_iff_forall_ball` is the same criterion read on the concrete exhaustion of the
  grid by the sets `ballCells r` of cells whose coordinates are at most `r` in absolute value.
-/

namespace StickPolyhex

variable {n : ℕ}

/-- A label of a cell: the orientation of the stick covering it and the index, counted from
`0`, of the cell inside that stick. -/
structure StickLabel (n : ℕ) where
  /-- The orientation of the stick covering the cell. -/
  dir : HexDir
  /-- The index of the cell inside its stick, counted from `0`. -/
  idx : Fin n
deriving DecidableEq

instance : Finite (StickLabel n) :=
  Finite.of_injective (fun l => (l.dir, l.idx)) (by rintro ⟨d, i⟩ ⟨d', i'⟩ h; simpa using h)

instance : TopologicalSpace (StickLabel n) := ⊥

instance : DiscreteTopology (StickLabel n) := ⟨rfl⟩

/-- A labelling of the hexagonal grid: an orientation and an index for every cell. -/
abbrev Labelling (n : ℕ) := Hex → StickLabel n

namespace Labelling

variable (R : EdgeRules n) (f : Labelling n)

/-- The orientation recorded at a cell. -/
def dir (c : Hex) : HexDir := (f c).dir

/-- The index recorded at a cell, counted from `1`. -/
def idx (c : Hex) : ℕ := (f c).idx + 1

lemma one_le_idx (c : Hex) : 1 ≤ f.idx c := Nat.le_add_left _ _

lemma idx_le (c : Hex) : f.idx c ≤ n := (f c).idx.2

/-- The label carried by the edge in direction `e` of the cell `c`, according to the rules `R`
(`none` if the edge is interior to a stick). -/
def labelOf (c : Hex) (e : HexDir) : Option R.Label :=
  R.frameLabel (f.idx c) (e - f.dir c + HexDir.W)

/-- All the conditions imposed at the cell `c`: the two local consistency rules of a stick
tiling, and the matching rules on the six edges of `c`. -/
def OKat (c : Hex) : Prop :=
  (f.idx c < n → f.dir (nbr c (f.dir c)) = f.dir c ∧ f.idx (nbr c (f.dir c)) = f.idx c + 1) ∧
  (1 < f.idx c →
    f.dir (nbr c (f.dir c).opp) = f.dir c ∧ f.idx (nbr c (f.dir c).opp) = f.idx c - 1) ∧
  (∀ (e : HexDir) (p q : R.Label), f.labelOf R c e = some p →
    f.labelOf R (nbr c e) e.opp = some q → ¬ R.Forbidden p q)

variable {R f}

/-- The labelling attached to a stick tiling. -/
def _root_.StickPolyhex.StickTiling.toLabelling (T : StickTiling n) : Labelling n := fun c =>
  ⟨T.dir c, ⟨T.idx c - 1, by have := T.idx_le c; have := T.idx_pos c; omega⟩⟩

@[simp] lemma toLabelling_dir (T : StickTiling n) (c : Hex) : T.toLabelling.dir c = T.dir c := rfl

@[simp] lemma toLabelling_idx (T : StickTiling n) (c : Hex) : T.toLabelling.idx c = T.idx c := by
  have := T.idx_pos c
  simp only [Labelling.idx, StickTiling.toLabelling]
  omega

@[simp] lemma labelOf_toLabelling (T : StickTiling n) (R : EdgeRules n) (c : Hex) (e : HexDir) :
    T.toLabelling.labelOf R c e = T.labelOf R c e := by
  simp only [Labelling.labelOf, StickTiling.labelOf, toLabelling_dir, toLabelling_idx]

/-- The stick tiling described by a globally consistent labelling. -/
def toStickTiling (h : ∀ c, f.OKat R c) : StickTiling n where
  dir := f.dir
  idx := f.idx
  idx_pos := f.one_le_idx
  idx_le := f.idx_le
  succ_dir c hc := ((h c).1 hc).1
  succ_idx c hc := ((h c).1 hc).2
  pred_dir c hc := ((h c).2.1 hc).1
  pred_idx c hc := ((h c).2.1 hc).2

/-- A globally consistent labelling gives a tiling satisfying the rules, and conversely. -/
theorem exists_stickTiling_iff :
    (∃ f : Labelling n, ∀ c, f.OKat R c) ↔ ∃ T : StickTiling n, T.SatisfiesRules R := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨toStickTiling hf, fun c e p q hp hq => (hf c).2.2 e p q hp hq⟩
  · rintro ⟨T, hT⟩
    refine ⟨T.toLabelling, fun c => ⟨fun hc => ?_, fun hc => ?_, fun e p q hp hq => ?_⟩⟩
    · simp only [toLabelling_dir, toLabelling_idx] at hc ⊢
      exact ⟨T.succ_dir c hc, T.succ_idx c hc⟩
    · simp only [toLabelling_dir, toLabelling_idx] at hc ⊢
      exact ⟨T.pred_dir c hc, T.pred_idx c hc⟩
    · rw [labelOf_toLabelling] at hp hq
      exact hT c e p q hp hq

/-! ### Compactness -/

/-- The conditions at a cell only involve the cell and its six neighbours. -/
lemma okAt_congr {f g : Labelling n} {c : Hex}
    (h : ∀ e : HexDir, f (nbr c e) = g (nbr c e)) (hc : f c = g c) :
    f.OKat R c → g.OKat R c := by
  have hdir : g.dir c = f.dir c := by simp [Labelling.dir, hc]
  have hidx : g.idx c = f.idx c := by simp [Labelling.idx, hc]
  have hnbr : ∀ e : HexDir, g.dir (nbr c e) = f.dir (nbr c e) ∧
      g.idx (nbr c e) = f.idx (nbr c e) := by
    intro e
    constructor <;> simp [Labelling.dir, Labelling.idx, h e]
  have hlab : ∀ e : HexDir, g.labelOf R c e = f.labelOf R c e := by
    intro e; simp [Labelling.labelOf, hdir, hidx]
  have hlab' : ∀ e : HexDir, g.labelOf R (nbr c e) e.opp = f.labelOf R (nbr c e) e.opp := by
    intro e
    simp [Labelling.labelOf, (hnbr e).1, (hnbr e).2]
  rintro ⟨h1, h2, h3⟩
  refine ⟨fun hlt => ?_, fun hlt => ?_, fun e p q hp hq => ?_⟩
  · rw [hidx] at hlt ⊢
    rw [hdir, (hnbr (f.dir c)).1, (hnbr (f.dir c)).2]
    exact h1 hlt
  · rw [hidx] at hlt ⊢
    rw [hdir, (hnbr (f.dir c).opp).1, (hnbr (f.dir c).opp).2]
    exact h2 hlt
  · rw [hlab] at hp
    rw [hlab'] at hq
    exact h3 e p q hp hq

/-- The finite set of cells the conditions at `c` depend on: `c` itself and its six
neighbours. -/
def support (c : Hex) : Finset Hex :=
  insert c (Finset.univ.image fun e : HexDir => nbr c e)

lemma mem_support_self (c : Hex) : c ∈ support c := Finset.mem_insert_self _ _

lemma nbr_mem_support (c : Hex) (e : HexDir) : nbr c e ∈ support c :=
  Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨e, Finset.mem_univ _, rfl⟩)

/-- A set of labellings determined by the values on a finite set of cells is closed. -/
lemma isClosed_of_finite_support {s : Finset Hex} {P : Labelling n → Prop}
    (hP : ∀ f g : Labelling n, (∀ c ∈ s, f c = g c) → P f → P g) :
    IsClosed {f : Labelling n | P f} := by
  have key : ∀ Q : Labelling n → Prop, (∀ f g : Labelling n, (∀ c ∈ s, f c = g c) → Q f → Q g) →
      IsOpen {f : Labelling n | Q f} := by
    intro Q hQ
    rw [isOpen_iff_forall_mem_open]
    intro f hf
    refine ⟨{g : Labelling n | ∀ c ∈ s, g c = f c}, ?_, ?_, ?_⟩
    · intro g hg
      exact hQ f g (fun c hc => (hg c hc).symm) hf
    · have : {g : Labelling n | ∀ c ∈ s, g c = f c} =
          ⋂ c ∈ s, (fun g : Labelling n => g c) ⁻¹' {f c} := by
        ext g; simp [Set.mem_iInter]
      rw [this]
      exact isOpen_biInter_finset fun c _ =>
        (continuous_apply c).isOpen_preimage _ (isOpen_discrete _)
    · intro c _; rfl
  rw [← isOpen_compl_iff]
  have : {f : Labelling n | P f}ᶜ = {f : Labelling n | ¬ P f} := rfl
  rw [this]
  exact key _ fun f g hfg hnf hg => hnf (hP g f (fun c hc => (hfg c hc).symm) hg)

/-- **Compactness.**  If every finite set of cells admits a labelling satisfying all the
conditions imposed at its cells, then there is a labelling satisfying the conditions at every
cell. -/
theorem exists_forall_okAt_of_finset [NeZero n]
    (h : ∀ s : Finset Hex, ∃ f : Labelling n, ∀ c ∈ s, f.OKat R c) :
    ∃ f : Labelling n, ∀ c, f.OKat R c := by
  classical
  have : Nonempty (StickLabel n) := ⟨⟨HexDir.E, ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩⟩
  set K : Finset Hex → Set (Labelling n) := fun s => {f | ∀ c ∈ s, f.OKat R c} with hK
  have hclosed : ∀ s, IsClosed (K s) := by
    intro s
    have hsupp : ∀ f g : Labelling n,
        (∀ c ∈ s.biUnion support, f c = g c) → (∀ c ∈ s, f.OKat R c) → ∀ c ∈ s, g.OKat R c := by
      intro f g hfg hf c hc
      refine okAt_congr (fun e => hfg _ ?_) (hfg _ ?_) (hf c hc)
      · exact Finset.mem_biUnion.2 ⟨c, hc, nbr_mem_support c e⟩
      · exact Finset.mem_biUnion.2 ⟨c, hc, mem_support_self c⟩
    exact isClosed_of_finite_support hsupp
  have hne : ∀ s, (K s).Nonempty := by
    intro s
    obtain ⟨f, hf⟩ := h s
    exact ⟨f, hf⟩
  have hdir : Directed (· ⊇ ·) K := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩ <;> intro f hf c hc <;> exact hf c (by simp [hc])
  have hcompact : ∀ s, IsCompact (K s) := fun s => (hclosed s).isCompact
  obtain ⟨f, hf⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hdir hne hcompact hclosed
  refine ⟨f, fun c => ?_⟩
  have := Set.mem_iInter.1 hf {c}
  exact this c (Finset.mem_singleton_self c)

end Labelling

/-- **The grid stick tiling problem is a local condition.**  The marked stick prototile described
by `d` tiles the hexagonal grid subject to its matching rules if and only if, for every finite
set `s` of cells, there is a labelling of the grid satisfying all the conditions imposed at the
cells of `s`. -/
theorem stickTilesGrid_iff_forall_finset (d : MarkData) :
    StickTilesGrid d ↔
      ∀ s : Finset Hex, ∃ f : Labelling (d.blockLen + 1), ∀ c ∈ s, f.OKat d.rules c := by
  constructor
  · intro h s
    obtain ⟨f, hf⟩ := Labelling.exists_stickTiling_iff.2 h
    exact ⟨f, fun c _ => hf c⟩
  · intro h
    exact Labelling.exists_stickTiling_iff.1 (Labelling.exists_forall_okAt_of_finset h)

/-- The cells whose two axial coordinates are at most `r` in absolute value. -/
noncomputable def ballCells (r : ℕ) : Finset Hex :=
  (Finset.Icc (-(r : ℤ)) r) ×ˢ (Finset.Icc (-(r : ℤ)) r)

lemma exists_ballCells_superset (s : Finset Hex) : ∃ r : ℕ, s ⊆ ballCells r := by
  refine ⟨s.sup fun c => max c.1.natAbs c.2.natAbs, fun c hc => ?_⟩
  have hle : max c.1.natAbs c.2.natAbs ≤ s.sup fun c => max c.1.natAbs c.2.natAbs :=
    Finset.le_sup (f := fun c : Hex => max c.1.natAbs c.2.natAbs) hc
  have h1 : c.1.natAbs ≤ s.sup fun c => max c.1.natAbs c.2.natAbs :=
    le_trans (le_max_left _ _) hle
  have h2 : c.2.natAbs ≤ s.sup fun c => max c.1.natAbs c.2.natAbs :=
    le_trans (le_max_right _ _) hle
  simp only [ballCells, Finset.mem_product, Finset.mem_Icc]
  omega

/-- **The local criterion on balls.**  The marked stick prototile described by `d` tiles the
hexagonal grid subject to its matching rules if and only if, for every `r`, the cells whose
coordinates are at most `r` in absolute value carry a labelling satisfying all the conditions
imposed at them. -/
theorem stickTilesGrid_iff_forall_ball (d : MarkData) :
    StickTilesGrid d ↔
      ∀ r : ℕ, ∃ f : Labelling (d.blockLen + 1), ∀ c ∈ ballCells r, f.OKat d.rules c := by
  rw [stickTilesGrid_iff_forall_finset]
  refine ⟨fun h r => h _, fun h s => ?_⟩
  obtain ⟨r, hr⟩ := exists_ballCells_superset s
  obtain ⟨f, hf⟩ := h r
  exact ⟨f, fun c hc => hf c (hr hc)⟩

end StickPolyhex
