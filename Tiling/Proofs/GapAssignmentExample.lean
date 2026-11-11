import Tiling.Proofs.GapRealization

/-!
# A concrete family of states and values

To see that the hypotheses of `Schematic.exists_of_gapAssignment` are satisfiable, this file
exhibits the simplest instance of the data of Section 2.5 — one bucket, one value, the interval
`{0}` — together with the constant states and values, and deduces from the general construction
that they are realised by a schematic and by a tiling of the plane.
-/

namespace StickPolyhex

namespace GapSpec

/-- The simplest instance of the data of Section 2.5: one bucket, one value `1`, and the
interval `I 1 = {0}`. -/
def trivialSpec : GapSpec where
  s := 1
  v := 1
  hs := le_rfl
  hv := le_rfl
  L _ := {1}
  R _ := {1}
  hL _ := by rintro a rfl; simp
  hR _ := by rintro a rfl; simp
  Imin _ := 0
  Imax _ := 0
  hImin _ := by norm_num
  hImax _ := by norm_num
  hI _ := le_rfl

@[simp] lemma trivialSpec_blockLen : trivialSpec.blockLen = 4 := by
  norm_num [blockLen, lb, trivialSpec]

end GapSpec

/-- The constant states and values for `GapSpec.trivialSpec`: every row has state `1` and both
values of every gap are `1`. -/
def trivialAssignment : GapAssignment GapSpec.trivialSpec where
  st _ := 1
  xv _ _ := 1
  yv _ _ := 1
  state_mem _ := ⟨le_rfl, le_rfl⟩
  state_cycle _ := rfl
  x_mem _ _ := rfl
  y_mem _ _ := rfl
  value_sum _ _ := rfl
  interval _ _ := by norm_num [GapSpec.trivialSpec]

/-- The data of `trivialAssignment` is realised by a schematic, and hence by a tiling of the
plane by the stick of length `5` decorated with the corresponding marks. -/
theorem exists_trivial_tiling :
    ∃ T : StickTiling (GapSpec.trivialSpec.blockLen + 1),
      T.SatisfiesRules (markedRules GapSpec.trivialSpec.blockLen GapSpec.trivialSpec.marking) ∧
        T.FormsWeavePattern :=
  GapSpec.exists_tiling_of_gapAssignment trivialAssignment

end StickPolyhex
