/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackForgetComparison
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelComparison

/-! # The original supported tensor unitor after forgetting support

The actual tensor unitor on a supported pulled-back object retains its original ambient
component in both directions through the full-subcategory inclusion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- The genuine supported tensor unitor retains its original ambient forward component. -/
theorem tensorPairUnitor_forget_hom_app
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).map ((tensorPairUnitor p).hom.app K) =
      (boundedFlatPerfectTensorUnitPullbackIso p.hom.right).hom.app
        ((tensorCoefficientSupportedForget B.obj.hom).obj K) := by
  apply (boundedFlatPerfect A.obj.right).ι.map_injective
  change (boundedFlatPerfectSupported A.obj.hom).ι.map
      ((tensorPairUnitor p).hom.app K) = _
  simp only [tensorPairUnitor, isoWhiskerLeft_hom, whiskerLeft_app,
    boundedFlatPerfectTensorUnitPullbackIso_hom_app,
    boundedFlatPerfectSupportedTensorUnitIso, fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, boundedFlatPerfectTensorUnitIso_hom_original]
  rfl

/-- The whole actual tensor unitor is retained under support-forgetting. -/
theorem tensorPairUnitor_forget_iso_app
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).mapIso ((tensorPairUnitor p).app K) =
      (boundedFlatPerfectTensorUnitPullbackIso p.hom.right).app
        ((tensorCoefficientSupportedForget B.obj.hom).obj K) := by
  apply Iso.ext
  exact tensorPairUnitor_forget_hom_app p K

/-- The genuine supported tensor unitor retains its original ambient inverse component. -/
theorem tensorPairUnitor_forget_inv_app
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).map ((tensorPairUnitor p).inv.app K) =
      (boundedFlatPerfectTensorUnitPullbackIso p.hom.right).inv.app
        ((tensorCoefficientSupportedForget B.obj.hom).obj K) :=
  congrArg Iso.inv (tensorPairUnitor_forget_iso_app p K)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
