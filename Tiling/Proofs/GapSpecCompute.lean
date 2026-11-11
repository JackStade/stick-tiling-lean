import Tiling.Proofs.GapSpecMarks

/-!
# The marks are computed from the finite data by a primitive recursive function

`GapSpecData.markData` turns the finite bucket data into the marked stick prototile that the
construction of Section 2.5 places on a block.  This file proves that this is done by a
*primitive recursive*, hence computable, function of the data: `GapSpecData.markData_primrec`.

The `GapSpecData` are encoded as the tuple of their six fields, which makes them a `Primcodable`
type, and the lists of marks are built from the parameters by list operations (`List.range`,
`List.flatMap`, `List.map`) and arithmetic on natural numbers, all of which are primitive
recursive.
-/

namespace StickPolyhex

open Primrec

/-- A `GapSpecData` is the tuple of its six fields. -/
def GapSpecData.equivTuple :
    GapSpecData ≃ ℕ × ℕ × List (List ℕ) × List (List ℕ) × List ℕ × List ℕ where
  toFun G := (G.sRaw, G.vRaw, G.Lraw, G.Rraw, G.IloRaw, G.IhiRaw)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv := by intro G; cases G; rfl
  right_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl

instance : Primcodable GapSpecData := Primcodable.ofEquiv _ GapSpecData.equivTuple

namespace GapSpecData

theorem equivTuple_primrec : Primrec (fun G : GapSpecData => GapSpecData.equivTuple G) :=
  Primrec.of_equiv

theorem sRaw_primrec : Primrec GapSpecData.sRaw :=
  Primrec.fst.comp equivTuple_primrec

theorem vRaw_primrec : Primrec GapSpecData.vRaw :=
  Primrec.fst.comp (Primrec.snd.comp equivTuple_primrec)

theorem Lraw_primrec : Primrec GapSpecData.Lraw :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp equivTuple_primrec))

theorem Rraw_primrec : Primrec GapSpecData.Rraw :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivTuple_primrec)))

theorem IloRaw_primrec : Primrec GapSpecData.IloRaw :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp equivTuple_primrec))))

theorem IhiRaw_primrec : Primrec GapSpecData.IhiRaw :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp equivTuple_primrec))))

theorem s_primrec : Primrec GapSpecData.s :=
  (Primrec.nat_max.comp sRaw_primrec (Primrec.const 1)).of_eq fun _ => rfl

theorem v_primrec : Primrec GapSpecData.v :=
  (Primrec.nat_max.comp vRaw_primrec (Primrec.const 1)).of_eq fun _ => rfl

theorem lb_primrec : Primrec GapSpecData.lb :=
  (Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) v_primrec)
        (Primrec.const 1))
      (Primrec.nat_sub.comp s_primrec (Primrec.const 1)))
    (Primrec.nat_mul.comp (Primrec.const 2) v_primrec)).of_eq fun _ => rfl

theorem blockLen_primrec : Primrec GapSpecData.blockLen :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp s_primrec lb_primrec)
    (Primrec.const 2)).of_eq fun _ => rfl


theorem ilo_primrec : Primrec₂ GapSpecData.ilo := by
  have hget : Primrec (fun p : GapSpecData × ℕ => (p.1.IloRaw[p.2]?).getD p.1.v) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (IloRaw_primrec.comp Primrec.fst) Primrec.snd)
      (v_primrec.comp Primrec.fst)
  have h : Primrec (fun p : GapSpecData × ℕ =>
      min (max ((p.1.IloRaw[p.2]?).getD p.1.v) 1) (2 * p.1.v - 1)) :=
    Primrec.nat_min.comp (Primrec.nat_max.comp hget (Primrec.const 1))
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (v_primrec.comp Primrec.fst)) (Primrec.const 1))
  refine h.of_eq fun p => ?_
  simp only [GapSpecData.ilo, List.getD_eq_getElem?_getD]

theorem ihi_primrec : Primrec₂ GapSpecData.ihi := by
  have hget : Primrec (fun p : GapSpecData × ℕ => (p.1.IhiRaw[p.2]?).getD p.1.v) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (IhiRaw_primrec.comp Primrec.fst) Primrec.snd)
      (v_primrec.comp Primrec.fst)
  have h : Primrec (fun p : GapSpecData × ℕ =>
      max (GapSpecData.ilo p.1 p.2) (min (max ((p.1.IhiRaw[p.2]?).getD p.1.v) 1)
        (2 * p.1.v - 1))) :=
    Primrec.nat_max.comp (ilo_primrec.comp Primrec.fst Primrec.snd)
      (Primrec.nat_min.comp (Primrec.nat_max.comp hget (Primrec.const 1))
        (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (v_primrec.comp Primrec.fst)) (Primrec.const 1)))
  refine h.of_eq fun p => ?_
  simp only [GapSpecData.ihi, List.getD_eq_getElem?_getD]

theorem Lval_primrec : Primrec₂ GapSpecData.Lval := by
  have hget : Primrec (fun p : GapSpecData × ℕ => p.1.Lraw.getD p.2 []) :=
    (Primrec.list_getD []).comp (Lraw_primrec.comp Primrec.fst) Primrec.snd
  have hg : Primrec₂ (fun (p : GapSpecData × ℕ) (b : ℕ) =>
      if 1 ≤ b ∧ b ≤ p.1.v then [b] else []) :=
    Primrec.ite
      (PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.nat_le.comp Primrec.snd (v_primrec.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.const [])
  exact (Primrec.list_flatMap hget hg).of_eq fun p => rfl

theorem Rval_primrec : Primrec₂ GapSpecData.Rval := by
  have hget : Primrec (fun p : GapSpecData × ℕ => p.1.Rraw.getD p.2 []) :=
    (Primrec.list_getD []).comp (Rraw_primrec.comp Primrec.fst) Primrec.snd
  have hg : Primrec₂ (fun (p : GapSpecData × ℕ) (b : ℕ) =>
      if 1 ≤ b ∧ b ≤ p.1.v then [b] else []) :=
    Primrec.ite
      (PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.nat_le.comp Primrec.snd (v_primrec.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.const [])
  exact (Primrec.list_flatMap hget hg).of_eq fun p => rfl

theorem sigma_primrec : Primrec₂ GapSpecData.sigma := by
  have h : Primrec (fun p : GapSpecData × ℕ => if p.2 = p.1.s then 1 else p.2 + 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (s_primrec.comp Primrec.fst))
      (Primrec.const 1) (Primrec.succ.comp Primrec.snd)
  exact h.of_eq fun p => rfl


/-! ### The lists of marks -/

private theorem bucketRange_primrec :
    Primrec (fun G : GapSpecData => List.range (G.s + 1)) :=
  Primrec.list_range.comp (Primrec.succ.comp s_primrec)

theorem topArrowLList_primrec : Primrec GapSpecData.topArrowLList := by
  have h1 : Primrec (fun G : GapSpecData =>
      (List.range G.s).flatMap (fun k => if 1 ≤ k then [k * G.lb] else [])) :=
    Primrec.list_flatMap (Primrec.list_range.comp s_primrec)
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.nat_mul.comp Primrec.snd (lb_primrec.comp Primrec.fst)) (Primrec.const []))
        (Primrec.const []))
  have h2 : Primrec (fun G : GapSpecData =>
      (List.range (G.s + 1)).flatMap (fun k =>
        if 1 ≤ k then [(k - 1) * G.lb + (2 * G.v - 1) * (k - 1) + (2 * G.v + 1 - G.ilo k)]
        else [])) :=
    Primrec.list_flatMap bucketRange_primrec
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.nat_add.comp
            (Primrec.nat_add.comp
              (Primrec.nat_mul.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
                (lb_primrec.comp Primrec.fst))
              (Primrec.nat_mul.comp
                (Primrec.nat_sub.comp
                  (Primrec.nat_mul.comp (Primrec.const 2) (v_primrec.comp Primrec.fst))
                  (Primrec.const 1))
                (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))))
            (Primrec.nat_sub.comp
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp (Primrec.const 2) (v_primrec.comp Primrec.fst))
                (Primrec.const 1))
              (ilo_primrec.comp Primrec.fst Primrec.snd)))
          (Primrec.const []))
        (Primrec.const []))
  have h3 : Primrec (fun G : GapSpecData =>
      (List.range (G.v + 1)).flatMap (fun a =>
        if 1 ≤ a ∧ a + G.v < G.ilo 1 then [G.v + 1 - a] else [])) :=
    Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp v_primrec))
      (Primrec.ite
        (PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
          (Primrec.nat_lt.comp
            (Primrec.nat_add.comp Primrec.snd (v_primrec.comp Primrec.fst))
            (ilo_primrec.comp Primrec.fst (Primrec.const 1))))
        (Primrec.list_cons.comp
          (Primrec.nat_sub.comp
            (Primrec.nat_add.comp (v_primrec.comp Primrec.fst) (Primrec.const 1))
            Primrec.snd)
          (Primrec.const []))
        (Primrec.const []))
  exact (Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3).of_eq fun G => rfl

theorem topArrowRList_primrec : Primrec GapSpecData.topArrowRList := by
  have h1 : Primrec (fun G : GapSpecData =>
      (List.range G.s).flatMap (fun k => if 1 ≤ k then [k * G.lb] else [])) :=
    Primrec.list_flatMap (Primrec.list_range.comp s_primrec)
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.nat_mul.comp Primrec.snd (lb_primrec.comp Primrec.fst)) (Primrec.const []))
        (Primrec.const []))
  have h2 : Primrec (fun G : GapSpecData =>
      (List.range (G.s + 1)).flatMap (fun k =>
        if 1 ≤ k then [(k - 1) * G.lb + (2 * G.v - 1) * (k - 1) + (2 * G.v - 1 - G.ihi k)]
        else [])) :=
    Primrec.list_flatMap bucketRange_primrec
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.nat_add.comp
            (Primrec.nat_add.comp
              (Primrec.nat_mul.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
                (lb_primrec.comp Primrec.fst))
              (Primrec.nat_mul.comp
                (Primrec.nat_sub.comp
                  (Primrec.nat_mul.comp (Primrec.const 2) (v_primrec.comp Primrec.fst))
                  (Primrec.const 1))
                (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))))
            (Primrec.nat_sub.comp
              (Primrec.nat_sub.comp
                (Primrec.nat_mul.comp (Primrec.const 2) (v_primrec.comp Primrec.fst))
                (Primrec.const 1))
              (ihi_primrec.comp Primrec.fst Primrec.snd)))
          (Primrec.const []))
        (Primrec.const []))
  have h3 : Primrec (fun G : GapSpecData =>
      (List.range (G.v + 1)).flatMap (fun b =>
        if 1 ≤ b ∧ b + G.ihi G.s < G.v then [G.s * G.lb - G.v + b - 1] else [])) :=
    Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp v_primrec))
      (Primrec.ite
        (PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
          (Primrec.nat_lt.comp
            (Primrec.nat_add.comp Primrec.snd
              (ihi_primrec.comp Primrec.fst (s_primrec.comp Primrec.fst)))
            (v_primrec.comp Primrec.fst)))
        (Primrec.list_cons.comp
          (Primrec.nat_sub.comp
            (Primrec.nat_add.comp
              (Primrec.nat_sub.comp
                (Primrec.nat_mul.comp (s_primrec.comp Primrec.fst)
                  (lb_primrec.comp Primrec.fst))
                (v_primrec.comp Primrec.fst))
              Primrec.snd)
            (Primrec.const 1))
          (Primrec.const []))
        (Primrec.const []))
  exact (Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3).of_eq fun G => rfl

theorem botArrowLList_primrec : Primrec GapSpecData.botArrowLList := by
  have h : Primrec (fun G : GapSpecData =>
      (List.range (G.s + 1)).flatMap (fun i =>
        if 1 ≤ i then [(G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v + 1]
        else [])) :=
    Primrec.list_flatMap bucketRange_primrec
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.nat_add.comp
            (Primrec.nat_add.comp
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp
                  (Primrec.nat_sub.comp (s_primrec.comp Primrec.fst) Primrec.snd)
                  (lb_primrec.comp Primrec.fst))
                (Primrec.nat_mul.comp
                  (Primrec.nat_sub.comp
                    (Primrec.nat_mul.comp (Primrec.const 2) (v_primrec.comp Primrec.fst))
                    (Primrec.const 1))
                  (Primrec.nat_sub.comp (sigma_primrec.comp Primrec.fst Primrec.snd)
                    (Primrec.const 1))))
              (v_primrec.comp Primrec.fst))
            (Primrec.const 1))
          (Primrec.const []))
        (Primrec.const []))
  exact h.of_eq fun G => rfl

theorem botArrowRList_primrec : Primrec GapSpecData.botArrowRList := by
  have h : Primrec (fun G : GapSpecData =>
      (List.range (G.s + 1)).flatMap (fun i =>
        if 1 ≤ i then [(G.s - i) * G.lb + (2 * G.v - 1) * (G.sigma i - 1) + G.v - 1]
        else [])) :=
    Primrec.list_flatMap bucketRange_primrec
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.nat_sub.comp
            (Primrec.nat_add.comp
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp
                  (Primrec.nat_sub.comp (s_primrec.comp Primrec.fst) Primrec.snd)
                  (lb_primrec.comp Primrec.fst))
                (Primrec.nat_mul.comp
                  (Primrec.nat_sub.comp
                    (Primrec.nat_mul.comp (Primrec.const 2) (v_primrec.comp Primrec.fst))
                    (Primrec.const 1))
                  (Primrec.nat_sub.comp (sigma_primrec.comp Primrec.fst Primrec.snd)
                    (Primrec.const 1))))
              (v_primrec.comp Primrec.fst))
            (Primrec.const 1))
          (Primrec.const []))
        (Primrec.const []))
  exact h.of_eq fun G => rfl

theorem triangleLList_primrec : Primrec GapSpecData.triangleLList := by
  have hmap : Primrec (fun p : GapSpecData × ℕ =>
      (p.1.Lval p.2).map (fun b => p.2 * p.1.lb - p.1.v + b)) :=
    Primrec.list_map (Lval_primrec.comp Primrec.fst Primrec.snd)
      (Primrec.nat_add.comp
        (Primrec.nat_sub.comp
          (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst)
            (lb_primrec.comp (Primrec.fst.comp Primrec.fst)))
          (v_primrec.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd)
  have h : Primrec (fun G : GapSpecData =>
      (List.range (G.s + 1)).flatMap (fun k =>
        if 1 ≤ k then (G.Lval k).map (fun b => k * G.lb - G.v + b) else [])) :=
    Primrec.list_flatMap bucketRange_primrec
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        hmap (Primrec.const []))
  exact h.of_eq fun G => rfl

theorem triangleRList_primrec : Primrec GapSpecData.triangleRList := by
  have hmap : Primrec (fun p : GapSpecData × ℕ =>
      (p.1.Rval p.2).map (fun a => (p.2 - 1) * p.1.lb + p.1.v - a)) :=
    Primrec.list_map (Rval_primrec.comp Primrec.fst Primrec.snd)
      (Primrec.nat_sub.comp
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp
            (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
            (lb_primrec.comp (Primrec.fst.comp Primrec.fst)))
          (v_primrec.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd)
  have h : Primrec (fun G : GapSpecData =>
      (List.range (G.s + 1)).flatMap (fun k =>
        if 1 ≤ k then (G.Rval k).map (fun a => (k - 1) * G.lb + G.v - a) else [])) :=
    Primrec.list_flatMap bucketRange_primrec
      (Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
        hmap (Primrec.const []))
  exact h.of_eq fun G => rfl

/-- **The marks are computed by a primitive recursive function of the finite bucket data.** -/
theorem markData_primrec : Primrec GapSpecData.markData := by
  have hf : Primrec (fun G : GapSpecData =>
      (G.blockLen, G.topArrowLList, G.topArrowRList, G.botArrowLList, G.botArrowRList,
        G.triangleLList, G.triangleRList)) :=
    Primrec.pair blockLen_primrec
      (Primrec.pair topArrowLList_primrec
        (Primrec.pair topArrowRList_primrec
          (Primrec.pair botArrowLList_primrec
            (Primrec.pair botArrowRList_primrec
              (Primrec.pair triangleLList_primrec triangleRList_primrec)))))
  have h := (Primrec.of_equiv_symm_iff (e := MarkData.equivTuple)
    (f := fun G : GapSpecData =>
      (G.blockLen, G.topArrowLList, G.topArrowRList, G.botArrowLList, G.botArrowRList,
        G.triangleLList, G.triangleRList))).2 hf
  exact h.of_eq fun G => rfl

end GapSpecData

end StickPolyhex


