/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelComparison
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationUnit

/-! # The genuine supported tensor coefficient through the complete Model comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.obj.right, ⊤))ˣ)

/-- The actual supported tensor unitor identifies the same objectwise forward scalar. -/
theorem tensorAutomorphism_scalar
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (tensorSupportedPairAutomorphism p r).hom.app K =
      (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r).hom.app
        ((tensorSupportedPairFunctor p).obj K) := by
  let L := (boundedFlatPerfectSupportedPullback p).obj K
  apply (cancel_mono ((boundedFlatPerfectSupportedTensorUnitIso A.obj.hom).hom.app L)).mp
  have h := NatTrans.congr_app
    (boundedFlatPerfectSupportedTensorUnitAutomorphism_unitor A.obj.hom r) L
  exact h.trans ((boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r).hom.naturality
    ((boundedFlatPerfectSupportedTensorUnitIso A.obj.hom).hom.app L))

local instance :
    (AsSmall.down :
      Quillen.Waldhausen.SmallModel ((boundedFlatPerfectSupported A.obj.hom).FullSubcategory) ⥤
      (boundedFlatPerfectSupported A.obj.hom).FullSubcategory).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- The fixed supported zero rebase keeps the original tensor multiplication component. -/
theorem tensorModelTransformation_scalar :
    tensorSupportedPairModelTransformation p r =
      (onFunctor (tensorSupportedPairModelMap p).functor
        (smallUnit (X := op A.obj.right) A.obj.hom r)).hom := by
  apply NatTrans.ext
  funext K
  change Quillen.Waldhausen.SmallModel
    ((boundedFlatPerfectSupported B.obj.hom).FullSubcategory) at K
  apply (AsSmall.down :
      Quillen.Waldhausen.SmallModel ((boundedFlatPerfectSupported A.obj.hom).FullSubcategory) ⥤
    (boundedFlatPerfectSupported A.obj.hom).FullSubcategory).map_injective
  rw [onFunctor_hom_app, smallUnit, map_lift_hom]
  simp only [tensorSupportedPairModelTransformation, whiskerLeft_app, whiskerRight_app,
    AsSmall.down_map, AsSmall.up_map_down, normalizedWeakTransformation, NatTrans.comp_app]
  rw [tensorAutomorphism_scalar]
  let z := tensorSupportedPairNormalization p
  have hn := (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r).hom.naturality
    (z.hom.app (AsSmall.down.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  change z.inv.app (AsSmall.down.obj K) ≫
      (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r).hom.app
        ((tensorSupportedPairFunctor p).obj (AsSmall.down.obj K)) ≫
      z.hom.app (AsSmall.down.obj K) =
    (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r).hom.app
      ((tensorSupportedPairNormalizedFunctor p).obj (AsSmall.down.obj K))
  rw [← hn, Iso.inv_hom_id_app_assoc]
  rfl

/-- The full actual supported Model iso intertwines the internal and genuine tensor units. -/
theorem internalTensorModelIso_unit :
    whiskerRight
      (onFunctor (supportedPairModelMap p).functor
        (unit (X := op A.obj.right) A.obj.hom r)).hom
      (evaluationModel (X := op A.obj.right) A.obj.hom).functor ≫
      (internalTensorModelIso p).hom =
    (internalTensorModelIso p).hom ≫
      whiskerLeft (evaluationModel (X := op B.obj.right) B.obj.hom).functor
        (tensorSupportedPairModelTransformation p r) := by
  rw [tensorModelTransformation_scalar]
  exact onFunctor_whisker_square (supportedPairModelMap p).functor
    (tensorSupportedPairModelMap p).functor
    (evaluationModel (X := op B.obj.right) B.obj.hom).functor
    (evaluationModel (X := op A.obj.right) A.obj.hom).functor
    (internalTensorModelIso p).hom
    (unit (X := op A.obj.right) A.obj.hom r)
    (smallUnit (X := op A.obj.right) A.obj.hom r)
    (evaluationModel_unit (X := op A.obj.right) A.obj.hom r).whisker

end Quillen.PerfectComplexes.SupportedTensorEvaluation
