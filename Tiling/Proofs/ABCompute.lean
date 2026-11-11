import Tiling.Proofs.ABSpecEquiv
import Tiling.Proofs.GapSpecCompute

/-!
# The bucket data of an AB tile set is computed by a primitive recursive function

This file proves that `ABSim.abSpecData`, the finite bucket data attached to a set of AB tiles by
Sections 2.6–2.8, is computed by a primitive recursive function of the tile set
(`ABSim.abSpecData_primrec`): the numbers `t`, `K`, `P`, `d`, `v` and `s`, the four matching
functions, the lists of values of every bucket and the two ends of every interval are all
obtained by arithmetic and list operations.
-/

namespace StickPolyhex

namespace ABSim

open Tiling.AB Primrec

/-! ### Tiles and tile sets -/

theorem ABTile_ul_primrec : Primrec ABTile.ul :=
  Primrec.fst.comp (Primrec.of_equiv (e := ABTile.equivTuple))

theorem ABTile_ur_primrec : Primrec ABTile.ur :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := ABTile.equivTuple)))

theorem ABTile_ll_primrec : Primrec ABTile.ll :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := ABTile.equivTuple))))

theorem ABTile_lr_primrec : Primrec ABTile.lr :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := ABTile.equivTuple))))

theorem A_primrec : Primrec ABTileSet.A :=
  Primrec.fst.comp (Primrec.of_equiv (e := ABTileSet.equivProd))

theorem B_primrec : Primrec ABTileSet.B :=
  Primrec.snd.comp (Primrec.of_equiv (e := ABTileSet.equivProd))

/-! ### The numerical parameters -/

theorem tN_primrec : Primrec tN :=
  (Primrec.nat_max.comp (Primrec.list_length.comp A_primrec)
    (Primrec.list_length.comp B_primrec)).of_eq fun _ => rfl

lemma maxColor_eq_foldr (l : List ABTile) :
    maxColor l = l.foldr (fun u m => max (max u.ul u.ur) (max (max u.ll u.lr) m)) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [maxColor, List.foldr_cons, ih]

theorem maxColor_primrec : Primrec maxColor := by
  have h : Primrec (fun l : List ABTile =>
      l.foldr (fun u m => max (max u.ul u.ur) (max (max u.ll u.lr) m)) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp
        (Primrec.nat_max.comp (ABTile_ul_primrec.comp (Primrec.fst.comp Primrec.snd))
          (ABTile_ur_primrec.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.nat_max.comp
          (Primrec.nat_max.comp (ABTile_ll_primrec.comp (Primrec.fst.comp Primrec.snd))
            (ABTile_lr_primrec.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun l => (maxColor_eq_foldr l).symm

theorem kN_primrec : Primrec kN :=
  (Primrec.succ.comp (maxColor_primrec.comp
    (Primrec.list_append.comp A_primrec B_primrec))).of_eq fun _ => rfl

theorem pN_primrec : Primrec pN :=
  (Primrec.nat_max.comp (Primrec.nat_sub.comp tN_primrec (Primrec.const 1))
    (Primrec.const 1)).of_eq fun _ => rfl

theorem dN_primrec : Primrec dN :=
  (Primrec.nat_mul.comp (Primrec.const 12)
    (Primrec.nat_add.comp kN_primrec tN_primrec)).of_eq fun _ => rfl

theorem vN_primrec : Primrec vN :=
  (Primrec.nat_mul.comp dN_primrec
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) tN_primrec))).of_eq fun _ => rfl

theorem sN_primrec : Primrec sN :=
  (Primrec.nat_add.comp (Primrec.const 16)
    (Primrec.nat_mul.comp (Primrec.const 8) pN_primrec)).of_eq fun _ => rfl

/-! ### The colors -/

theorem tileAN_primrec : Primrec₂ tileAN :=
  ((Primrec.list_getD dfltTile).comp (A_primrec.comp Primrec.fst)
    (Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
      (Primrec.list_length.comp (A_primrec.comp Primrec.fst)))).of_eq fun _ => rfl

theorem tileBN_primrec : Primrec₂ tileBN :=
  ((Primrec.list_getD dfltTile).comp (B_primrec.comp Primrec.fst)
    (Primrec.nat_mod.comp
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
        (tN_primrec.comp Primrec.fst))
      (Primrec.list_length.comp (B_primrec.comp Primrec.fst)))).of_eq fun _ => rfl

theorem hcolorN_primrec {f g : ABTile → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun p : ABTileSet × ℕ => hcolorN p.1 f g p.2) := by
  have h : Primrec (fun p : ABTileSet × ℕ =>
      if p.2 ≤ tN p.1 then f (tileAN p.1 p.2) else g (tileBN p.1 p.2)) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd (tN_primrec.comp Primrec.fst))
      (hf.comp (tileAN_primrec.comp Primrec.fst Primrec.snd))
      (hg.comp (tileBN_primrec.comp Primrec.fst Primrec.snd))
  exact h.of_eq fun p => rfl

private theorem gN_primrec_aux {f g : ABTile → ℕ} (hf : Primrec f) (hg : Primrec g)
    (c₁ c₂ : ℕ) :
    Primrec (fun p : ABTileSet × ℕ =>
      (if p.2 ≤ tN p.1 then c₁ * kN p.1 else c₂ * kN p.1) + hcolorN p.1 f g p.2) :=
  Primrec.nat_add.comp
    (Primrec.ite (Primrec.nat_le.comp Primrec.snd (tN_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (Primrec.const c₁) (kN_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (Primrec.const c₂) (kN_primrec.comp Primrec.fst)))
    (hcolorN_primrec hf hg)

theorem g₁N_primrec : Primrec₂ g₁N :=
  (gN_primrec_aux ABTile_ur_primrec ABTile_ll_primrec 2 4).of_eq fun p => by
    simp only [g₁N]

theorem g₂N_primrec : Primrec₂ g₂N :=
  (gN_primrec_aux ABTile_ul_primrec ABTile_lr_primrec 4 2).of_eq fun p => by
    simp only [g₂N]

theorem g₃N_primrec : Primrec₂ g₃N :=
  (gN_primrec_aux ABTile_lr_primrec ABTile_ul_primrec 2 4).of_eq fun p => by
    simp only [g₃N]

theorem g₄N_primrec : Primrec₂ g₄N :=
  (gN_primrec_aux ABTile_ll_primrec ABTile_ur_primrec 4 2).of_eq fun p => by
    simp only [g₄N]


/-! ### The lists of values -/

theorem slotList_primrec {α : Type*} [Primcodable α] {lo hi : α → ℕ} {f : α → ℕ → ℕ}
    (hlo : Primrec lo) (hhi : Primrec hi) (hf : Primrec₂ f) :
    Primrec (fun a => slotList (lo a) (hi a) (f a)) := by
  have h : Primrec (fun a => (List.range (hi a + 1 - lo a)).map (fun i => f a (lo a + i))) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_sub.comp (Primrec.succ.comp hhi) hlo))
      (hf.comp Primrec.fst
        (Primrec.nat_add.comp (hlo.comp Primrec.fst) Primrec.snd)).to₂
  exact h.of_eq fun a => rfl

theorem slotList2_primrec {α : Type*} [Primcodable α] {lo hi lo' hi' : α → ℕ}
    {f : α → ℕ → ℕ → ℕ} (hlo : Primrec lo) (hhi : Primrec hi) (hlo' : Primrec lo')
    (hhi' : Primrec hi') (hf : Primrec (fun p : (α × ℕ) × ℕ => f p.1.1 p.1.2 p.2)) :
    Primrec (fun a => slotList2 (lo a) (hi a) (lo' a) (hi' a) (f a)) := by
  have hid : Primrec (fun a => slotList (lo a) (hi a) id) :=
    slotList_primrec hlo hhi (Primrec.snd).to₂
  have hinner : Primrec (fun p : α × ℕ => slotList (lo' p.1) (hi' p.1) (f p.1 p.2)) :=
    slotList_primrec (hlo'.comp Primrec.fst) (hhi'.comp Primrec.fst) hf.to₂
  exact (Primrec.list_flatMap hid hinner.to₂).of_eq fun a => rfl

theorem EfullL_primrec : Primrec EfullL :=
  (slotList_primrec (Primrec.const 1) vN_primrec (Primrec.snd).to₂).of_eq fun _ => rfl

theorem EsetL_primrec : Primrec EsetL :=
  (slotList_primrec (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) tN_primrec)
    (Primrec.nat_mul.comp (dN_primrec.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

theorem AsetL_primrec : Primrec AsetL := by
  have h1 : Primrec (fun S : ABTileSet =>
      slotList 1 (2 * tN S) (fun l => dN S * l + 2 * kN S)) :=
    slotList_primrec (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 2) tN_primrec)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (dN_primrec.comp Primrec.fst) Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.const 2) (kN_primrec.comp Primrec.fst))).to₂
  have h2 : Primrec (fun S : ABTileSet =>
      slotList2 1 (2 * tN S) 0 (2 * kN S - 2) (fun l e => dN S * l + e - (3 * kN S - 1))) :=
    slotList2_primrec (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 2) tN_primrec)
      (Primrec.const 0)
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) kN_primrec)
        (Primrec.const 2))
      (Primrec.nat_sub.comp
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp Primrec.fst))
          Primrec.snd)
        (Primrec.nat_sub.comp
          (Primrec.nat_mul.comp (Primrec.const 3)
            (kN_primrec.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.const 1)))
  exact (Primrec.list_append.comp h1 h2).of_eq fun _ => rfl

theorem RloadL_primrec {gN : ABTileSet → ℕ → ℕ} (hg : Primrec₂ gN) :
    Primrec (fun S : ABTileSet => RloadL S (gN S)) :=
  (slotList_primrec (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 2) tN_primrec)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (dN_primrec.comp Primrec.fst) Primrec.snd)
      (hg.comp Primrec.fst Primrec.snd)).to₂).of_eq fun _ => rfl

theorem RresetL_primrec : Primrec RresetL :=
  (slotList2_primrec (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 2) tN_primrec)
    (Primrec.const 0)
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 6) kN_primrec)
      (Primrec.const 1))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)).of_eq fun _ => rfl

theorem C₁L_primrec : Primrec (fun q : ABTileSet × ℕ => C₁L q.1 q.2) := by
  have h1 : Primrec (fun q : ABTileSet × ℕ =>
      slotList 1 (tN q.1) (fun l => dN q.1 * l)) :=
    slotList_primrec (Primrec.const 1) (tN_primrec.comp Primrec.fst)
      (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  have h2 : Primrec (fun q : ABTileSet × ℕ =>
      slotList (tN q.1 + 1) (max (tN q.1 + 1) (2 * tN q.1 - q.2))
        (fun l => dN q.1 * l + q.2)) :=
    slotList_primrec (Primrec.succ.comp (tN_primrec.comp Primrec.fst))
      (Primrec.nat_max.comp (Primrec.succ.comp (tN_primrec.comp Primrec.fst))
        (Primrec.nat_sub.comp
          (Primrec.nat_mul.comp (Primrec.const 2) (tN_primrec.comp Primrec.fst)) Primrec.snd))
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.snd.comp Primrec.fst)).to₂
  exact (Primrec.ite
    (Primrec.nat_le.comp Primrec.snd (pN_primrec.comp Primrec.fst))
    (Primrec.list_append.comp h1 h2) (Primrec.const [])).of_eq fun _ => rfl

theorem D₁L_primrec : Primrec (fun q : ABTileSet × ℕ => D₁L q.1 q.2) := by
  have h1 : Primrec (fun q : ABTileSet × ℕ =>
      slotList 1 (tN q.1) (fun l => dN q.1 * l)) :=
    slotList_primrec (Primrec.const 1) (tN_primrec.comp Primrec.fst)
      (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  have h2 : Primrec (fun q : ABTileSet × ℕ =>
      slotList (tN q.1 + 1) (min (2 * tN q.1) (tN q.1 + 1 + q.2))
        (fun l => dN q.1 * l + (pN q.1 - q.2))) :=
    slotList_primrec (Primrec.succ.comp (tN_primrec.comp Primrec.fst))
      (Primrec.nat_min.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (tN_primrec.comp Primrec.fst))
        (Primrec.nat_add.comp (Primrec.succ.comp (tN_primrec.comp Primrec.fst)) Primrec.snd))
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.nat_sub.comp (pN_primrec.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))).to₂
  exact (Primrec.ite
    (Primrec.nat_le.comp Primrec.snd (pN_primrec.comp Primrec.fst))
    (Primrec.list_append.comp h1 h2) (Primrec.const [])).of_eq fun _ => rfl

theorem C₂L_primrec : Primrec (fun q : ABTileSet × ℕ => C₂L q.1 q.2) := by
  have h1 : Primrec (fun q : ABTileSet × ℕ =>
      slotList (tN q.1 + 1) (2 * tN q.1) (fun l => dN q.1 * l)) :=
    slotList_primrec (Primrec.succ.comp (tN_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (Primrec.const 2) (tN_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  have h2 : Primrec (fun q : ABTileSet × ℕ =>
      slotList (min (tN q.1) (1 + q.2)) (tN q.1) (fun l => dN q.1 * l - q.2)) :=
    slotList_primrec
      (Primrec.nat_min.comp (tN_primrec.comp Primrec.fst)
        (Primrec.nat_add.comp (Primrec.const 1) Primrec.snd))
      (tN_primrec.comp Primrec.fst)
      (Primrec.nat_sub.comp
        (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.snd.comp Primrec.fst)).to₂
  refine (Primrec.ite
    (Primrec.nat_le.comp Primrec.snd (pN_primrec.comp Primrec.fst))
    (Primrec.list_append.comp h1 h2) (Primrec.const [])).of_eq fun q => ?_
  simp only [C₂L]

theorem D₂L_primrec : Primrec (fun q : ABTileSet × ℕ => D₂L q.1 q.2) := by
  have h1 : Primrec (fun q : ABTileSet × ℕ =>
      slotList (tN q.1 + 1) (2 * tN q.1) (fun l => dN q.1 * l)) :=
    slotList_primrec (Primrec.succ.comp (tN_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (Primrec.const 2) (tN_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  have h2 : Primrec (fun q : ABTileSet × ℕ =>
      slotList (max 1 (tN q.1 - q.2)) (tN q.1) (fun l => dN q.1 * l - (pN q.1 - q.2))) :=
    slotList_primrec
      (Primrec.nat_max.comp (Primrec.const 1)
        (Primrec.nat_sub.comp (tN_primrec.comp Primrec.fst) Primrec.snd))
      (tN_primrec.comp Primrec.fst)
      (Primrec.nat_sub.comp
        (Primrec.nat_mul.comp (dN_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.nat_sub.comp (pN_primrec.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))).to₂
  exact (Primrec.ite
    (Primrec.nat_le.comp Primrec.snd (pN_primrec.comp Primrec.fst))
    (Primrec.list_append.comp h1 h2) (Primrec.const [])).of_eq fun _ => rfl


/-! ### The bucket table -/

/-- The data of a bucket is the tuple of its four fields. -/
def BucketData.equivTuple : BucketData ≃ List ℕ × List ℕ × ℕ × ℕ where
  toFun b := (b.L, b.R, b.lo, b.hi)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by intro b; cases b; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

instance : Primcodable BucketData := Primcodable.ofEquiv _ BucketData.equivTuple

theorem bucket_primrec {α : Type*} [Primcodable α] {L R : α → List ℕ} {lo hi : α → ℕ}
    (hL : Primrec L) (hR : Primrec R) (hlo : Primrec lo) (hhi : Primrec hi) :
    Primrec (fun a => (⟨L a, R a, lo a, hi a⟩ : BucketData)) := by
  have hf : Primrec (fun a => (L a, R a, lo a, hi a)) :=
    Primrec.pair hL (Primrec.pair hR (Primrec.pair hlo hhi))
  have h := (Primrec.of_equiv_symm_iff (e := BucketData.equivTuple)
    (f := fun a => (L a, R a, lo a, hi a))).2 hf
  exact h.of_eq fun a => rfl

theorem BucketData_L_primrec : Primrec BucketData.L :=
  Primrec.fst.comp (Primrec.of_equiv (e := BucketData.equivTuple))

theorem BucketData_R_primrec : Primrec BucketData.R :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := BucketData.equivTuple)))

theorem BucketData_lo_primrec : Primrec BucketData.lo :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := BucketData.equivTuple))))

theorem BucketData_hi_primrec : Primrec BucketData.hi :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.of_equiv (e := BucketData.equivTuple))))

theorem matchList_primrec {gN : ABTileSet → ℕ → ℕ} (hg : Primrec₂ gN) :
    Primrec (fun q : ABTileSet × ℕ => matchList q.1 (gN q.1) q.2) := by
  have hE : Primrec (fun q : ABTileSet × ℕ => EfullL q.1) := EfullL_primrec.comp Primrec.fst
  have hEs : Primrec (fun q : ABTileSet × ℕ => EsetL q.1) := EsetL_primrec.comp Primrec.fst
  have hA : Primrec (fun q : ABTileSet × ℕ => AsetL q.1) := AsetL_primrec.comp Primrec.fst
  have hR : Primrec (fun q : ABTileSet × ℕ => RloadL q.1 (gN q.1)) :=
    (RloadL_primrec hg).comp Primrec.fst
  have hRreset : Primrec (fun q : ABTileSet × ℕ => RresetL q.1) :=
    RresetL_primrec.comp Primrec.fst
  have hv : Primrec (fun q : ABTileSet × ℕ => vN q.1) := vN_primrec.comp Primrec.fst
  have hvk : Primrec (fun q : ABTileSet × ℕ => vN q.1 + 6 * kN q.1) :=
    Primrec.nat_add.comp hv
      (Primrec.nat_mul.comp (Primrec.const 6) (kN_primrec.comp Primrec.fst))
  exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      (bucket_primrec hE hR hv hvk)
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 2))
        (bucket_primrec hEs hA hv hvk)
        (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 3))
          (bucket_primrec hE hRreset hv hvk)
          (bucket_primrec hEs hEs hv hvk)))).of_eq fun _ => rfl

theorem freeList₁_primrec : Primrec (fun q : ABTileSet × ℕ => freeList₁ q.1 q.2) := by
  have hE : Primrec (fun q : ABTileSet × ℕ => EfullL q.1) := EfullL_primrec.comp Primrec.fst
  have hEs : Primrec (fun q : ABTileSet × ℕ => EsetL q.1) := EsetL_primrec.comp Primrec.fst
  have hv : Primrec (fun q : ABTileSet × ℕ => vN q.1) := vN_primrec.comp Primrec.fst
  have hd : Primrec (fun q : ABTileSet × ℕ => dN q.1) := dN_primrec.comp Primrec.fst
  have hp : Primrec (fun q : ABTileSet × ℕ => pN q.1) := pN_primrec.comp Primrec.fst
  have hC : Primrec (fun q : ABTileSet × ℕ => C₁L q.1 ((q.2 + 1) / 2)) :=
    C₁L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp (Primrec.succ.comp Primrec.snd) (Primrec.const 2)))
  have hC' : Primrec (fun q : ABTileSet × ℕ => C₁L q.1 (q.2 / 2)) :=
    C₁L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)))
  have hD : Primrec (fun q : ABTileSet × ℕ => D₁L q.1 ((q.2 - 2 * pN q.1 + 1) / 2)) :=
    D₁L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp
        (Primrec.succ.comp
          (Primrec.nat_sub.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp)))
        (Primrec.const 2)))
  have hD' : Primrec (fun q : ABTileSet × ℕ => D₁L q.1 ((q.2 - 2 * pN q.1) / 2)) :=
    D₁L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp
        (Primrec.nat_sub.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp))
        (Primrec.const 2)))
  have hlast : Primrec (fun q : ABTileSet × ℕ =>
      if q.2 = 4 * pN q.1 then EsetL q.1 else EfullL q.1) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 4) hp))
      hEs hE
  exact (Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp))
      (Primrec.ite
        (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1))
        (bucket_primrec hE hC
          (Primrec.succ.comp (Primrec.nat_sub.comp hv hd)) (Primrec.succ.comp hv))
        (bucket_primrec hC' hE hv hv))
      (Primrec.ite
        (Primrec.eq.comp
          (Primrec.nat_mod.comp
            (Primrec.nat_sub.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp))
            (Primrec.const 2))
          (Primrec.const 1))
        (bucket_primrec hE hD (Primrec.nat_sub.comp hv (Primrec.const 1))
          (Primrec.nat_sub.comp (Primrec.nat_add.comp hv hd) (Primrec.const 1)))
        (bucket_primrec hD' hlast hv hv))).of_eq fun _ => rfl

theorem freeList₂_primrec : Primrec (fun q : ABTileSet × ℕ => freeList₂ q.1 q.2) := by
  have hE : Primrec (fun q : ABTileSet × ℕ => EfullL q.1) := EfullL_primrec.comp Primrec.fst
  have hv : Primrec (fun q : ABTileSet × ℕ => vN q.1) := vN_primrec.comp Primrec.fst
  have hd : Primrec (fun q : ABTileSet × ℕ => dN q.1) := dN_primrec.comp Primrec.fst
  have hp : Primrec (fun q : ABTileSet × ℕ => pN q.1) := pN_primrec.comp Primrec.fst
  have hC : Primrec (fun q : ABTileSet × ℕ => C₂L q.1 ((q.2 + 1) / 2)) :=
    C₂L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp (Primrec.succ.comp Primrec.snd) (Primrec.const 2)))
  have hC' : Primrec (fun q : ABTileSet × ℕ => C₂L q.1 (q.2 / 2)) :=
    C₂L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)))
  have hD : Primrec (fun q : ABTileSet × ℕ => D₂L q.1 ((q.2 - 2 * pN q.1 + 1) / 2)) :=
    D₂L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp
        (Primrec.succ.comp
          (Primrec.nat_sub.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp)))
        (Primrec.const 2)))
  have hD' : Primrec (fun q : ABTileSet × ℕ => D₂L q.1 ((q.2 - 2 * pN q.1) / 2)) :=
    D₂L_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.nat_div.comp
        (Primrec.nat_sub.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp))
        (Primrec.const 2)))
  exact (Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp))
      (Primrec.ite
        (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1))
        (bucket_primrec hE hC (Primrec.nat_sub.comp hv (Primrec.const 1))
          (Primrec.nat_sub.comp (Primrec.nat_add.comp hv hd) (Primrec.const 1)))
        (bucket_primrec hC' hE hv hv))
      (Primrec.ite
        (Primrec.eq.comp
          (Primrec.nat_mod.comp
            (Primrec.nat_sub.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) hp))
            (Primrec.const 2))
          (Primrec.const 1))
        (bucket_primrec hE hD
          (Primrec.succ.comp (Primrec.nat_sub.comp hv hd)) (Primrec.succ.comp hv))
        (bucket_primrec hD' hE hv hv))).of_eq fun _ => rfl

theorem dataList_primrec : Primrec (fun q : ABTileSet × ℕ => dataList q.1 q.2) := by
  have hEs : Primrec (fun q : ABTileSet × ℕ => EsetL q.1) := EsetL_primrec.comp Primrec.fst
  have hv : Primrec (fun q : ABTileSet × ℕ => vN q.1) := vN_primrec.comp Primrec.fst
  have hp : Primrec (fun q : ABTileSet × ℕ => pN q.1) := pN_primrec.comp Primrec.fst
  have hs : Primrec (fun q : ABTileSet × ℕ => sN q.1) := sN_primrec.comp Primrec.fst
  have shift : ∀ c : ℕ, Primrec (fun q : ABTileSet × ℕ => (q.1, q.2 - c)) := fun c =>
    Primrec.pair Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const c))
  have shiftP : ∀ c : ℕ, Primrec (fun q : ABTileSet × ℕ => (q.1, q.2 - c - 4 * pN q.1)) :=
    fun c => Primrec.pair Primrec.fst
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const c))
        (Primrec.nat_mul.comp (Primrec.const 4) hp))
  have h1 := (matchList_primrec g₁N_primrec).comp (shift 1)
  have h2 := (matchList_primrec g₂N_primrec).comp (shift 5)
  have h3 := (matchList_primrec g₃N_primrec).comp (shiftP 9)
  have h4 := (matchList_primrec g₄N_primrec).comp (shiftP 13)
  have hf1 := freeList₁_primrec.comp (shift 9)
  have hf2 := freeList₂_primrec.comp (shiftP 17)
  exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      (bucket_primrec hEs hEs hv hv)
      (Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.const 5)) h1
        (Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.const 9)) h2
          (Primrec.ite (Primrec.nat_le.comp Primrec.snd
              (Primrec.nat_add.comp (Primrec.const 9)
                (Primrec.nat_mul.comp (Primrec.const 4) hp))) hf1
            (Primrec.ite (Primrec.nat_le.comp Primrec.snd
                (Primrec.nat_add.comp (Primrec.const 13)
                  (Primrec.nat_mul.comp (Primrec.const 4) hp))) h3
              (Primrec.ite (Primrec.nat_le.comp Primrec.snd
                  (Primrec.nat_add.comp (Primrec.const 17)
                    (Primrec.nat_mul.comp (Primrec.const 4) hp))) h4
                (Primrec.ite (Primrec.nat_le.comp Primrec.snd hs) hf2
                  (bucket_primrec (Primrec.const []) (Primrec.const []) hv
                    hv)))))))).of_eq fun _ => rfl

/-! ### The finite specification -/

/-- **The finite bucket data is computed by a primitive recursive function of the tile set.** -/
theorem abSpecData_primrec : Primrec abSpecData := by
  have hrange : Primrec (fun S : ABTileSet => List.range (sN S + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp sN_primrec)
  have hdl : Primrec₂ (fun (S : ABTileSet) (q : ℕ) => dataList S q) := dataList_primrec.to₂
  have hL : Primrec (fun S : ABTileSet =>
      (List.range (sN S + 1)).map (fun q => (dataList S q).L)) :=
    Primrec.list_map hrange (BucketData_L_primrec.comp (hdl.comp Primrec.fst Primrec.snd)).to₂
  have hR : Primrec (fun S : ABTileSet =>
      (List.range (sN S + 1)).map (fun q => (dataList S q).R)) :=
    Primrec.list_map hrange (BucketData_R_primrec.comp (hdl.comp Primrec.fst Primrec.snd)).to₂
  have hlo : Primrec (fun S : ABTileSet =>
      (List.range (sN S + 1)).map (fun q => (dataList S q).lo)) :=
    Primrec.list_map hrange (BucketData_lo_primrec.comp (hdl.comp Primrec.fst Primrec.snd)).to₂
  have hhi : Primrec (fun S : ABTileSet =>
      (List.range (sN S + 1)).map (fun q => (dataList S q).hi)) :=
    Primrec.list_map hrange (BucketData_hi_primrec.comp (hdl.comp Primrec.fst Primrec.snd)).to₂
  have hf : Primrec (fun S : ABTileSet =>
      (sN S, vN S, (List.range (sN S + 1)).map (fun q => (dataList S q).L),
        (List.range (sN S + 1)).map (fun q => (dataList S q).R),
        (List.range (sN S + 1)).map (fun q => (dataList S q).lo),
        (List.range (sN S + 1)).map (fun q => (dataList S q).hi))) :=
    Primrec.pair sN_primrec (Primrec.pair vN_primrec
      (Primrec.pair hL (Primrec.pair hR (Primrec.pair hlo hhi))))
  have h := (Primrec.of_equiv_symm_iff (e := GapSpecData.equivTuple)
    (f := fun S : ABTileSet =>
      (sN S, vN S, (List.range (sN S + 1)).map (fun q => (dataList S q).L),
        (List.range (sN S + 1)).map (fun q => (dataList S q).R),
        (List.range (sN S + 1)).map (fun q => (dataList S q).lo),
        (List.range (sN S + 1)).map (fun q => (dataList S q).hi)))).2 hf
  exact h.of_eq fun S => rfl

end ABSim

end StickPolyhex


