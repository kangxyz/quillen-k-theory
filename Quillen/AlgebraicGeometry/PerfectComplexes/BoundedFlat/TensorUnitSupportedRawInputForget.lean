/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackInputForgetIso
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedUnitorForgetIso
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRawInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawInputSquare

/-! # The whole original tensor input comparison after forgetting support

The original tensor input comparison is conjugation of the independent geometric input
comparison by its actual tensor unitors. Forgetting support preserves all three whole
isomorphisms and therefore preserves the original raw tensor input comparison itself.
No component of the five-factor composite is expanded.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The original supported tensor input comparison is conjugation of the geometric square. -/
theorem tensorSupportedRawInputIso_conjugatePullback :
    tensorSupportedRawInputIso p q a b h =
      isoWhiskerRight (SupportedTensorEvaluation.tensorPairUnitor p)
          (boundedFlatPerfectSupportedPullback a) ≪≫
        supportedPullbackInputSquareIso p q a b h ≪≫
        isoWhiskerLeft (boundedFlatPerfectSupportedPullback b)
          (SupportedTensorEvaluation.tensorPairUnitor q).symm := by
  simp only [tensorSupportedRawInputIso, supportedPullbackInputSquareIso, Iso.trans_assoc]

/-- The original ambient tensor input comparison is conjugation of the geometric square. -/
theorem tensorUnitRawInputIso_conjugatePullback {E F G H : Scheme.{u}}
    (p : E ⟶ F) (q : G ⟶ H) (a : G ⟶ E) (b : H ⟶ F) (h : a ≫ p = q ≫ b) :
    tensorUnitRawInputIso p q a b h =
      isoWhiskerRight (boundedFlatPerfectTensorUnitPullbackIso p)
          (boundedFlatPerfectPullback a) ≪≫
        pullbackInputSquareIso p q a b h ≪≫
        isoWhiskerLeft (boundedFlatPerfectPullback b)
          (boundedFlatPerfectTensorUnitPullbackIso q).symm := by
  simp only [tensorUnitRawInputIso, pullbackInputSquareIso, Iso.trans_assoc]

/-- The entire original supported tensor input comparison has its actual ambient image. -/
theorem tensorSupportedRawInputIso_forget :
    isoWhiskerRight (tensorSupportedRawInputIso p q a b h)
        (tensorCoefficientSupportedForget C.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
        (tensorUnitRawInputIso p.hom.right q.hom.right a.hom.right b.hom.right
          (congrArg (fun f : C ⟶ B => f.hom.right) h)) := by
  rw [tensorSupportedRawInputIso_conjugatePullback, tensorUnitRawInputIso_conjugatePullback]
  simp only [isoWhiskerRight_trans,
    SupportedTensorEvaluation.tensorPairUnitor_whiskerRight_forget,
    supportedPullbackInputSquareIso_forget,
    SupportedTensorEvaluation.tensorPairUnitor_whiskerLeft_symm_forget,
    isoWhiskerLeft_trans]

/-- Each raw tensor input component follows from the original whole-isomorphism comparison. -/
theorem tensorSupportedRawInputIso_forget_hom_app
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget C.obj.hom).map
        ((tensorSupportedRawInputIso p q a b h).hom.app K) =
      (tensorUnitRawInputIso p.hom.right q.hom.right a.hom.right b.hom.right
        (congrArg (fun f : C ⟶ B => f.hom.right) h)).hom.app
          ((tensorCoefficientSupportedForget B.obj.hom).obj K) :=
  NatTrans.congr_app (congrArg Iso.hom (tensorSupportedRawInputIso_forget p q a b h)) K

end Quillen.PerfectComplexes
