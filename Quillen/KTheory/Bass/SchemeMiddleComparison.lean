/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeContractionMiddle
public import Quillen.KTheory.Bass.TwoChartMiddleBiproduct

/-!
# Pointwise and natural presentations of the original scheme Bass middle row

The common-corner equation identifies the original pointwise chart presentation with the
natural scheme middle short complex. Both actual arrows are retained in this comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Bass.TwoChart
universe u w
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

/-- The two original charts coincide on the literal coefficient projection. -/
theorem bassCommonCorner :
    NatTrans.op polynomialProjection ≫ NatTrans.op plus =
      NatTrans.op polynomialProjection ≫ NatTrans.op minus := by
  apply NatTrans.ext
  funext X
  apply Quiver.Hom.unop_inj
  exact (plus_projection X.unop).trans (minus_projection X.unop).symm

/-- The actual pointwise Bass row is the original natural scheme row. -/
def bassMiddlePointwiseIso
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    middleComplex (NatTrans.op polynomialProjection) (NatTrans.op plus)
      (NatTrans.op minus) bassCommonCorner F ≅ bassMiddleComplex F :=
  by
  let e := polynomialPairBiprodIso (NatTrans.op plus) (NatTrans.op minus) F
  refine ShortComplex.isoMk (Iso.refl F) e (Iso.refl (laurentFunctor.op ⋙ F)) ?_ ?_
  · change 𝟙 F ≫ biprod.lift _ _ =
      middleCorner (NatTrans.op polynomialProjection) (NatTrans.op plus)
        (NatTrans.op minus) F ≫ e.hom
    rw [Category.id_comp]
    apply biprod.hom_ext
    · rw [biprod.lift_fst, Category.assoc, polynomialPairBiprodIso_hom_fst]
      apply NatTrans.ext
      funext X
      exact (biprod.lift_fst _ _).symm
    · rw [biprod.lift_snd, Category.assoc, polynomialPairBiprodIso_hom_snd]
      apply NatTrans.ext
      funext X
      exact (biprod.lift_snd _ _).symm
  · change e.hom ≫ biprod.desc _ _ =
      middleDifference (NatTrans.op plus) (NatTrans.op minus) F ≫ 𝟙 _
    rw [Category.comp_id]
    apply (cancel_epi e.inv).mp
    rw [Iso.inv_hom_id_assoc]
    change biprod.desc _ _ = biprod.desc _ _ ≫
      middleDifference (NatTrans.op plus) (NatTrans.op minus) F
    apply biprod.hom_ext'
    · rw [biprod.inl_desc, biprod.inl_desc_assoc]
      apply NatTrans.ext
      funext X
      exact (biprod.inl_desc _ _).symm
    · rw [biprod.inr_desc, biprod.inr_desc_assoc]
      apply NatTrans.ext
      funext X
      exact (biprod.inr_desc _ _).symm

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
