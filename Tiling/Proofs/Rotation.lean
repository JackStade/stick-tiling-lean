import Tiling.Proofs.Weave
import Tiling.Proofs.EdgeRules

/-!
# Rotating a stick tiling

The notion of a weave pattern (`StickTiling.IsWeavePattern`) depends on a choice of orientation
`u : HexDir`, and a tiling *forms* a weave pattern (`StickTiling.FormsWeavePattern`) when *some*
orientation works.  Several later results, in particular
`StickTiling.exists_schematic_respectsMarking`, are stated for the *normalised* orientation
`HexDir.W`.  This file supplies the missing normalisation step: rotating the whole picture.

The hexagonal grid is rotated by the automorphism `rotc k` of the axial coordinates, which is
the rotation by `k` sixths of a turn; it maps the neighbour of `c` in direction `e` to the
neighbour of `rotc k c` in direction `e + k` (`rotc_nbr`).  Transporting a tiling along it gives
`StickTiling.rotate T k`, and every notion entering the definition of a weave pattern is
equivariant: see `StickTiling.isWeavePattern_rotate` and `StickTiling.satisfiesRules_rotate`.
The conclusion is `StickTiling.exists_rotate_isWeavePattern_W`: a tiling satisfying a set of
edge rules and forming a weave pattern can be rotated into one which satisfies the same rules
and is a weave pattern for the orientation `HexDir.W`.
-/

namespace StickPolyhex

/-! ## Rotating the grid -/

/-- Rotation of the hexagonal grid by `60°`, in axial coordinates. -/
def rot1 (c : Hex) : Hex := (-c.2, c.1 + c.2)

/-- The inverse of `rot1`, i.e. the rotation by `-60°`. -/
def rot1inv (c : Hex) : Hex := (c.1 + c.2, -c.1)

/-- Rotation by `60°`, as an automorphism of the group of axial coordinates. -/
def rot1Aut : AddAut Hex where
  toFun := rot1
  invFun := rot1inv
  left_inv c := by simp [rot1, rot1inv]
  right_inv c := by simp [rot1, rot1inv]
  map_add' a b := by simp [rot1, Prod.ext_iff]; constructor <;> ring

/-- Rotation by `k` sixths of a turn, as an automorphism of the axial coordinates. -/
def rotAut (k : HexDir) : AddAut Hex := k.val • rot1Aut

/-- Rotation of the hexagonal grid by `k` sixths of a turn. -/
def rotc (k : HexDir) (c : Hex) : Hex := rotAut k c

/-- The inverse of the rotation `rotc k`. -/
def unrot (k : HexDir) (c : Hex) : Hex := (rotAut k).symm c

lemma rotAut_pow_apply (j : ℕ) (c : Hex) : (j • rot1Aut) c = rot1^[j] c := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    rw [succ_nsmul]
    show (j • rot1Aut) (rot1 c) = _
    rw [ih, Function.iterate_succ_apply]

lemma rot1_vec (d : HexDir) : rot1 d.vec = (d + 1).vec := by revert d; decide

lemma rot1_iterate_vec (j : ℕ) (d : HexDir) : rot1^[j] d.vec = (d + (j : HexDir)).vec := by
  induction j generalizing d with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, rot1_vec, ih]; push_cast; ring_nf

lemma natCast_val_hex (k : HexDir) : ((k.val : ℕ) : HexDir) = k := by
  simp [ZMod.natCast_val, ZMod.cast_id]

@[simp] lemma rotc_vec (k d : HexDir) : rotc k d.vec = (d + k).vec := by
  rw [rotc, rotAut, rotAut_pow_apply, rot1_iterate_vec, natCast_val_hex]

lemma rotc_add (k : HexDir) (a b : Hex) : rotc k (a + b) = rotc k a + rotc k b := map_add _ _ _

lemma rotc_zsmul (k : HexDir) (j : ℤ) (a : Hex) : rotc k (j • a) = j • rotc k a := map_zsmul _ _ _

/-- The rotation `rotc k` turns the neighbour in direction `e` into the neighbour in direction
`e + k`. -/
lemma rotc_nbr (k : HexDir) (c : Hex) (e : HexDir) :
    rotc k (nbr c e) = nbr (rotc k c) (e + k) := by
  rw [nbr, nbr, rotc_add, rotc_vec]

lemma rotc_walk (k : HexDir) (c : Hex) (d : HexDir) (j : ℤ) :
    rotc k (walk c d j) = walk (rotc k c) (d + k) j := by
  rw [walk, walk, rotc_add, rotc_zsmul, rotc_vec]

@[simp] lemma unrot_rotc (k : HexDir) (c : Hex) : unrot k (rotc k c) = c :=
  (rotAut k).symm_apply_apply c

@[simp] lemma rotc_unrot (k : HexDir) (c : Hex) : rotc k (unrot k c) = c :=
  (rotAut k).apply_symm_apply c

lemma rotc_injective (k : HexDir) : Function.Injective (rotc k) := (rotAut k).injective

lemma unrot_injective (k : HexDir) : Function.Injective (unrot k) := (rotAut k).symm.injective

lemma unrot_nbr (k : HexDir) (c : Hex) (e : HexDir) :
    unrot k (nbr c e) = nbr (unrot k c) (e - k) := by
  apply rotc_injective k
  rw [rotc_unrot, rotc_nbr, rotc_unrot, sub_add_cancel]

lemma unrot_walk (k : HexDir) (c : Hex) (d : HexDir) (j : ℤ) :
    unrot k (walk c d j) = walk (unrot k c) (d - k) j := by
  apply rotc_injective k
  rw [rotc_unrot, rotc_walk, rotc_unrot, sub_add_cancel]

/-! ## Rotating a tiling -/

namespace StickTiling

variable {n : ℕ} (T : StickTiling n) (k : HexDir)

/-- The tiling obtained by rotating `T` by `k` sixths of a turn. -/
def rotate : StickTiling n where
  dir c := T.dir (unrot k c) + k
  idx c := T.idx (unrot k c)
  idx_pos c := T.idx_pos _
  idx_le c := T.idx_le _
  succ_dir c h := by
    rw [unrot_nbr, add_sub_cancel_right, T.succ_dir _ h]
  succ_idx c h := by
    rw [unrot_nbr, add_sub_cancel_right, T.succ_idx _ h]
  pred_dir c h := by
    have he : (T.dir (unrot k c) + k).opp - k = (T.dir (unrot k c)).opp := by
      simp [HexDir.opp]; ring
    rw [unrot_nbr, he, T.pred_dir _ h]
  pred_idx c h := by
    have he : (T.dir (unrot k c) + k).opp - k = (T.dir (unrot k c)).opp := by
      simp [HexDir.opp]; ring
    rw [unrot_nbr, he, T.pred_idx _ h]

@[simp] lemma rotate_dir (c : Hex) : (T.rotate k).dir c = T.dir (unrot k c) + k := rfl

@[simp] lemma rotate_idx (c : Hex) : (T.rotate k).idx c = T.idx (unrot k c) := rfl


/-! ### Sticks -/

@[simp] lemma rotate_head (c : Hex) : (T.rotate k).head c = rotc k (T.head (unrot k c)) := by
  rw [head, head, rotate_dir, rotate_idx, rotc_walk, rotc_unrot]

@[simp] lemma rotate_cellOfStick (c : Hex) (j : ℕ) :
    (T.rotate k).cellOfStick c j = rotc k (T.cellOfStick (unrot k c) j) := by
  rw [cellOfStick, cellOfStick, rotate_head, rotate_dir, rotc_walk]

lemma mem_image_rotc {s : Finset Hex} {x : Hex} : x ∈ s.image (rotc k) ↔ unrot k x ∈ s := by
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rwa [unrot_rotc]
  · intro hx
    exact Finset.mem_image.2 ⟨unrot k x, hx, rotc_unrot k x⟩

@[simp] lemma rotate_stickOf (c : Hex) :
    (T.rotate k).stickOf c = (T.stickOf (unrot k c)).image (rotc k) := by
  rw [stickOf, stickOf, Finset.image_image]
  exact Finset.image_congr fun j _ => rotate_cellOfStick T k c j

/-! ### Stacked pairs -/

lemma sameAxis_add_right (d e f : HexDir) : SameAxis (d + f) e ↔ SameAxis d (e - f) := by
  revert d e f; decide

lemma sameAxis_add_add (d e f : HexDir) : SameAxis (d + f) (e + f) ↔ SameAxis d e := by
  revert d e f; decide

lemma rotate_stackedBy (a b : Hex) (e : HexDir) :
    (T.rotate k).StackedBy a b e ↔ T.StackedBy (unrot k a) (unrot k b) (e - k) := by
  rw [StackedBy, StackedBy, rotate_dir, rotate_dir, sameAxis_add_right,
    show T.dir (unrot k b) + k = (T.dir (unrot k b) - k) + k + k by ring,
    sameAxis_add_add, show T.dir (unrot k b) - k + k = T.dir (unrot k b) by ring]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h y hy
    have hy' : rotc k y ∈ (T.rotate k).stickOf a := by
      rw [rotate_stickOf, mem_image_rotc, unrot_rotc]; exact hy
    have := h _ hy'
    rw [rotate_stickOf, mem_image_rotc, unrot_nbr, unrot_rotc] at this
    exact this
  · intro h x hx
    rw [rotate_stickOf, mem_image_rotc] at hx
    rw [rotate_stickOf, mem_image_rotc, unrot_nbr]
    exact h _ hx

lemma rotate_isStackedPair (a b : Hex) :
    (T.rotate k).IsStackedPair a b ↔ T.IsStackedPair (unrot k a) (unrot k b) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e - k, (rotate_stackedBy T k a b e).1 he⟩
  · rintro ⟨e, he⟩
    refine ⟨e + k, (rotate_stackedBy T k a b (e + k)).2 ?_⟩
    rwa [add_sub_cancel_right]

lemma rotate_stackStep (a b : Hex) :
    (T.rotate k).StackStep a b ↔ T.StackStep (unrot k a) (unrot k b) := by
  rw [StackStep, StackStep, rotate_isStackedPair, rotate_stickOf, rotate_stickOf]
  exact or_congr (Finset.image_injective (rotc_injective k)).eq_iff Iff.rfl

lemma rotate_sameStack (a b : Hex) :
    (T.rotate k).SameStack a b ↔ T.SameStack (unrot k a) (unrot k b) := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail ((rotate_stackStep T k _ _).1 hstep)
  · intro h
    have key : ∀ x y : Hex, T.SameStack x y →
        (T.rotate k).SameStack (rotc k x) (rotc k y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        refine ih.tail ?_
        rw [rotate_stackStep, unrot_rotc, unrot_rotc]
        exact hstep
    have := key _ _ h
    rwa [rotc_unrot, rotc_unrot] at this

lemma rotate_stack (c : Hex) :
    (T.rotate k).Stack c = (fun s : Finset Hex => s.image (rotc k)) '' T.Stack (unrot k c) := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [rotate_sameStack] at hx
    exact ⟨T.stickOf (unrot k x), ⟨unrot k x, hx, rfl⟩, by rw [rotate_stickOf]⟩
  · rintro ⟨t, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨rotc k x, ?_, ?_⟩
    · simp only [rotate_sameStack, unrot_rotc]; exact hx
    · rw [rotate_stickOf, unrot_rotc]

lemma rotate_stackHeight (c : Hex) :
    (T.rotate k).stackHeight c = T.stackHeight (unrot k c) := by
  rw [stackHeight, stackHeight, rotate_stack]
  exact Set.ncard_image_of_injective _ (Finset.image_injective (rotc_injective k))

lemma rotate_leansLeft (a b : Hex) :
    (T.rotate k).LeansLeft a b ↔ T.LeansLeft (unrot k a) (unrot k b) := by
  constructor
  · rintro ⟨e, hst, he⟩
    refine ⟨e - k, (rotate_stackedBy T k a b e).1 hst, ?_⟩
    rw [rotate_dir] at he
    rcases he with he | he <;> [left; right] <;> rw [he] <;> ring
  · rintro ⟨e, hst, he⟩
    refine ⟨e + k, (rotate_stackedBy T k a b (e + k)).2 (by rwa [add_sub_cancel_right]), ?_⟩
    rw [rotate_dir]
    rcases he with he | he <;> [left; right] <;> rw [he] <;> ring

lemma rotate_leansRight (a b : Hex) :
    (T.rotate k).LeansRight a b ↔ T.LeansRight (unrot k a) (unrot k b) := by
  constructor
  · rintro ⟨e, hst, he⟩
    refine ⟨e - k, (rotate_stackedBy T k a b e).1 hst, ?_⟩
    rw [rotate_dir] at he
    rcases he with he | he <;> [left; right] <;> rw [he] <;> ring
  · rintro ⟨e, hst, he⟩
    refine ⟨e + k, (rotate_stackedBy T k a b (e + k)).2 (by rwa [add_sub_cancel_right]), ?_⟩
    rw [rotate_dir]
    rcases he with he | he <;> [left; right] <;> rw [he] <;> ring

lemma rotate_isLeftLeaningStack (c : Hex) :
    (T.rotate k).IsLeftLeaningStack c ↔ T.IsLeftLeaningStack (unrot k c) := by
  constructor
  · rintro ⟨a, b, hca, hab⟩
    exact ⟨unrot k a, unrot k b, (rotate_sameStack T k c a).1 hca,
      (rotate_leansLeft T k a b).1 hab⟩
  · rintro ⟨a, b, hca, hab⟩
    refine ⟨rotc k a, rotc k b, ?_, ?_⟩
    · simp only [rotate_sameStack, unrot_rotc]; exact hca
    · rw [rotate_leansLeft, unrot_rotc, unrot_rotc]; exact hab

lemma rotate_isRightLeaningStack (c : Hex) :
    (T.rotate k).IsRightLeaningStack c ↔ T.IsRightLeaningStack (unrot k c) := by
  constructor
  · rintro ⟨a, b, hca, hab⟩
    exact ⟨unrot k a, unrot k b, (rotate_sameStack T k c a).1 hca,
      (rotate_leansRight T k a b).1 hab⟩
  · rintro ⟨a, b, hca, hab⟩
    refine ⟨rotc k a, rotc k b, ?_, ?_⟩
    · simp only [rotate_sameStack, unrot_rotc]; exact hca
    · rw [rotate_leansRight, unrot_rotc, unrot_rotc]; exact hab

lemma rotate_slantsLeft (u : HexDir) (c : Hex) :
    (T.rotate k).SlantsLeft (u + k) c ↔ T.SlantsLeft u (unrot k c) := by
  rw [SlantsLeft, SlantsLeft, rotate_dir]
  constructor
  · rintro (h | h) <;> [left; right] <;>
      · have := congrArg (fun x : HexDir => x - k) h
        simpa using by linear_combination (norm := ring_nf) this
  · rintro (h | h) <;> [left; right] <;> rw [h] <;> ring

lemma rotate_stackAbove (u : HexDir) (a b : Hex) :
    (T.rotate k).StackAbove (u + k) a b ↔ T.StackAbove u (unrot k a) (unrot k b) := by
  rw [StackAbove, StackAbove]
  refine and_congr (not_congr (rotate_sameStack T k a b)) ?_
  constructor
  · rintro ⟨x, hx, hx'⟩
    refine ⟨unrot k x, (rotate_sameStack T k a x).1 hx, ?_⟩
    rcases hx' with h | h <;> [left; right] <;>
      · rw [rotate_sameStack, unrot_nbr] at h
        simp only [show u + k + 4 - k = u + 4 by ring,
          show u + k + 5 - k = u + 5 by ring] at h
        exact h
  · rintro ⟨x, hx, hx'⟩
    refine ⟨rotc k x, by simp only [rotate_sameStack, unrot_rotc]; exact hx, ?_⟩
    rcases hx' with h | h <;> [left; right] <;>
      · rw [rotate_sameStack, unrot_nbr, unrot_rotc]
        simp only [show u + k + 4 - k = u + 4 by ring,
          show u + k + 5 - k = u + 5 by ring]
        exact h

lemma rotate_stackBelow (u : HexDir) (a b : Hex) :
    (T.rotate k).StackBelow (u + k) a b ↔ T.StackBelow u (unrot k a) (unrot k b) := by
  rw [StackBelow, StackBelow]
  refine and_congr (not_congr (rotate_sameStack T k a b)) ?_
  constructor
  · rintro ⟨x, hx, hx'⟩
    refine ⟨unrot k x, (rotate_sameStack T k a x).1 hx, ?_⟩
    rcases hx' with h | h <;> [left; right] <;>
      · rw [rotate_sameStack, unrot_nbr] at h
        simp only [show u + k + 1 - k = u + 1 by ring,
          show u + k + 2 - k = u + 2 by ring] at h
        exact h
  · rintro ⟨x, hx, hx'⟩
    refine ⟨rotc k x, by simp only [rotate_sameStack, unrot_rotc]; exact hx, ?_⟩
    rcases hx' with h | h <;> [left; right] <;>
      · rw [rotate_sameStack, unrot_nbr, unrot_rotc]
        simp only [show u + k + 1 - k = u + 1 by ring,
          show u + k + 2 - k = u + 2 by ring]
        exact h

lemma rotate_stackAdjacent (a b : Hex) :
    (T.rotate k).StackAdjacent a b ↔ T.StackAdjacent (unrot k a) (unrot k b) := by
  rw [StackAdjacent, StackAdjacent]
  refine and_congr (not_congr (rotate_sameStack T k a b)) ?_
  constructor
  · rintro ⟨x, e, hx, hx'⟩
    refine ⟨unrot k x, e - k, (rotate_sameStack T k a x).1 hx, ?_⟩
    rw [rotate_sameStack, unrot_nbr] at hx'
    exact hx'
  · rintro ⟨x, e, hx, hx'⟩
    refine ⟨rotc k x, e + k, by simp only [rotate_sameStack, unrot_rotc]; exact hx, ?_⟩
    rw [rotate_sameStack, unrot_nbr, unrot_rotc, add_sub_cancel_right]
    exact hx'

/-! ### Edge rules -/

lemma rotate_labelOf (R : EdgeRules n) (c : Hex) (e : HexDir) :
    (T.rotate k).labelOf R c e = T.labelOf R (unrot k c) (e - k) := by
  rw [labelOf, labelOf, rotate_dir, rotate_idx]
  congr 1
  ring

/-- Satisfying a set of edge-matching rules is invariant under rotation. -/
lemma satisfiesRules_rotate {R : EdgeRules n} (h : T.SatisfiesRules R) :
    (T.rotate k).SatisfiesRules R := by
  intro c e p q hp hq
  rw [rotate_labelOf] at hp
  rw [rotate_labelOf, unrot_nbr, show e.opp - k = (e - k).opp by simp [HexDir.opp]; ring] at hq
  exact h _ _ p q hp hq

/-! ### The weave pattern -/

lemma rotate_dir_eq_iff (c : Hex) (w : HexDir) :
    (T.rotate k).dir c = w + k ↔ T.dir (unrot k c) = w := by
  rw [rotate_dir]
  constructor
  · intro h; have := congrArg (fun x : HexDir => x - k) h; simpa using this
  · intro h; rw [h]

/-- Rotating a weave pattern by `k` sixths of a turn gives a weave pattern for the orientation
rotated by the same amount. -/
theorem isWeavePattern_rotate {u : HexDir} (hw : T.IsWeavePattern u) :
    (T.rotate k).IsWeavePattern (u + k) := by
  constructor
  case horizontal_or_slantsLeft =>
    intro c
    rcases hw.horizontal_or_slantsLeft (unrot k c) with h | h
    · exact Or.inl ((rotate_dir_eq_iff T k c u).2 h)
    · exact Or.inr ((rotate_slantsLeft T k u c).2 h)
  case exists_horizontal =>
    obtain ⟨c, hc⟩ := hw.exists_horizontal
    exact ⟨rotc k c, (rotate_dir_eq_iff T k _ u).2 (by rwa [unrot_rotc])⟩
  case horizontal_leftLeaning =>
    intro c hc
    exact (rotate_isLeftLeaningStack T k c).2
      (hw.horizontal_leftLeaning _ ((rotate_dir_eq_iff T k c u).1 hc))
  case slantsLeft_rightLeaning =>
    intro c hc
    exact (rotate_isRightLeaningStack T k c).2
      (hw.slantsLeft_rightLeaning _ ((rotate_slantsLeft T k u c).1 hc))
  case horizontal_height =>
    intro c hc
    rw [rotate_stackHeight]
    exact hw.horizontal_height _ ((rotate_dir_eq_iff T k c u).1 hc)
  case two_above_two_below =>
    intro c hc
    obtain ⟨⟨a₁, a₂, ha₁, ha₂, hne, hab₁, hab₂, huniq⟩,
      ⟨b₁, b₂, hb₁, hb₂, hbne, hbb₁, hbb₂, hbuniq⟩⟩ :=
      hw.two_above_two_below _ ((rotate_dir_eq_iff T k c u).1 hc)
    constructor
    · refine ⟨rotc k a₁, rotc k a₂, (rotate_dir_eq_iff T k _ u).2 (by rwa [unrot_rotc]),
        (rotate_dir_eq_iff T k _ u).2 (by rwa [unrot_rotc]), ?_, ?_, ?_, ?_⟩
      · rw [rotate_sameStack, unrot_rotc, unrot_rotc]; exact hne
      · simp only [rotate_stackAbove, unrot_rotc]; exact hab₁
      · simp only [rotate_stackAbove, unrot_rotc]; exact hab₂
      · intro a hadir habove
        rw [rotate_dir_eq_iff] at hadir
        rw [rotate_stackAbove] at habove
        rcases huniq _ hadir habove with h | h
        · exact Or.inl (by simp only [rotate_sameStack, unrot_rotc]; exact h)
        · exact Or.inr (by simp only [rotate_sameStack, unrot_rotc]; exact h)
    · refine ⟨rotc k b₁, rotc k b₂, (rotate_dir_eq_iff T k _ u).2 (by rwa [unrot_rotc]),
        (rotate_dir_eq_iff T k _ u).2 (by rwa [unrot_rotc]), ?_, ?_, ?_, ?_⟩
      · rw [rotate_sameStack, unrot_rotc, unrot_rotc]; exact hbne
      · simp only [rotate_stackBelow, unrot_rotc]; exact hbb₁
      · simp only [rotate_stackBelow, unrot_rotc]; exact hbb₂
      · intro b hbdir hbelow
        rw [rotate_dir_eq_iff] at hbdir
        rw [rotate_stackBelow] at hbelow
        rcases hbuniq _ hbdir hbelow with h | h
        · exact Or.inl (by simp only [rotate_sameStack, unrot_rotc]; exact h)
        · exact Or.inr (by simp only [rotate_sameStack, unrot_rotc]; exact h)
  case overlap =>
    intro c c' hc hc' habove
    rw [rotate_dir_eq_iff] at hc hc'
    rw [rotate_stackAbove] at habove
    obtain ⟨x, hx, hxn, hx'⟩ := hw.overlap _ _ hc hc' habove
    refine ⟨rotc k x, by simp only [rotate_sameStack, unrot_rotc]; exact hx, ?_, ?_⟩
    · rw [rotate_idx, unrot_rotc]; exact hxn
    · rw [rotate_sameStack, unrot_nbr, unrot_rotc,
        show u + k + 5 - k = u + 5 by ring]
      exact hx'
  case grid_cell =>
    intro c a₁ a₂ hc ha₁ ha₂ hab₁ hab₂ hne
    rw [rotate_dir_eq_iff] at hc ha₁ ha₂
    rw [rotate_stackAbove] at hab₁ hab₂
    rw [rotate_sameStack] at hne
    obtain ⟨a₃, v, ha₃, h₁₃, h₂₃, hv, hvh, hvc, hv₁, hv₂, hv₃⟩ :=
      hw.grid_cell _ _ _ hc ha₁ ha₂ hab₁ hab₂ hne
    refine ⟨rotc k a₃, rotc k v, (rotate_dir_eq_iff T k _ u).2 (by rwa [unrot_rotc]), ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rotate_stackAbove, unrot_rotc]; exact h₁₃
    · simp only [rotate_stackAbove, unrot_rotc]; exact h₂₃
    · simp only [rotate_slantsLeft, unrot_rotc]; exact hv
    · simp only [rotate_stackHeight, unrot_rotc]; exact hvh
    · simp only [rotate_stackAdjacent, unrot_rotc]; exact hvc
    · simp only [rotate_stackAdjacent, unrot_rotc]; exact hv₁
    · simp only [rotate_stackAdjacent, unrot_rotc]; exact hv₂
    · simp only [rotate_stackAdjacent, unrot_rotc]; exact hv₃
  case no_back_to_back =>
    intro v v' hv hst
    rw [show u + k + 5 = (u + 5) + k by ring, rotate_dir_eq_iff] at hv
    rw [rotate_stackedBy, show u + k + 3 - k = u + 3 by ring] at hst
    have hnb := hw.no_back_to_back _ _ hv hst
    intro hcon
    exact hnb ((rotate_dir_eq_iff T k v' (u + 2)).1 (by rw [hcon]; ring))

/-- **Normalising the orientation.**  A tiling which satisfies a set of edge-matching rules and
forms a weave pattern can be rotated into one which satisfies the same rules and is a weave
pattern for the reference orientation `HexDir.W`. -/
theorem exists_isWeavePattern_W {R : EdgeRules n} (h : T.SatisfiesRules R)
    (hw : T.FormsWeavePattern) :
    ∃ T' : StickTiling n, T'.SatisfiesRules R ∧ T'.IsWeavePattern HexDir.W := by
  obtain ⟨u, hu⟩ := hw
  refine ⟨T.rotate (HexDir.W - u), satisfiesRules_rotate T _ h, ?_⟩
  have := isWeavePattern_rotate T (HexDir.W - u) hu
  rwa [show u + (HexDir.W - u) = HexDir.W by ring] at this

end StickTiling

end StickPolyhex
