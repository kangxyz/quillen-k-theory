/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedNormalizedInputUnit

/-! # The original tensor multiplication on the actual supported Model input square

The specified common-universe lift preserves the actual pulled-back scalar. Consequently the
independent raw Model input isomorphism intertwines the genuine normalized tensor transformations.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation

/-- The original supported geometric Model map preserves the actual small forward scalar. -/
theorem evaluationRawMap_preserves {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
    (r : (Γ(B.obj.right, ⊤))ˣ) :
    Preserves (evaluationRawMap p).functor (smallUnit (X := op B.obj.right) B.obj.hom r)
      (smallUnit (X := op A.obj.right) A.obj.hom
        (Units.map p.hom.right.appTop.hom.toMonoidHom r)) := by
  let : (AsSmall.down : SmallModel ((boundedFlatPerfectSupported A.obj.hom).FullSubcategory) ⥤
      (boundedFlatPerfectSupported A.obj.hom).FullSubcategory).IsEquivalence :=
    AsSmall.equiv.symm.isEquivalence_functor
  intro K
  change Quillen.Waldhausen.SmallModel
    ((boundedFlatPerfectSupported B.obj.hom).FullSubcategory) at K
  apply (AsSmall.down : SmallModel ((boundedFlatPerfectSupported A.obj.hom).FullSubcategory) ⥤
    (boundedFlatPerfectSupported A.obj.hom).FullSubcategory).map_injective
  change (normalizedPullback p).map
      (AsSmall.down.map ((smallUnit (X := op B.obj.right) B.obj.hom r).hom.app K)) =
    AsSmall.down.map
      ((smallUnit (X := op A.obj.right) A.obj.hom
        (Units.map p.hom.right.appTop.hom.toMonoidHom r)).hom.app
          (AsSmall.up.obj ((normalizedPullback p).obj (AsSmall.down.obj K))))
  rw [smallUnit, map_lift_hom, smallUnit, map_lift_hom]
  exact normalizedPullback_preserves p r (AsSmall.down.obj K)

/-- The full actual supported raw Model input square preserves genuine tensor multiplication. -/
theorem modelInputIso_unit {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
    (r : (Γ(A.obj.right, ⊤))ˣ) :
    whiskerRight (tensorSupportedPairModelTransformation p r) (evaluationRawMap a).functor ≫
        (tensorSupportedRawModelInputIso p q a b h).hom =
      (tensorSupportedRawModelInputIso p q a b h).hom ≫
        whiskerLeft (evaluationRawMap b).functor
          (tensorSupportedPairModelTransformation q
            (Units.map a.hom.right.appTop.hom.toMonoidHom r)) := by
  rw [tensorModelTransformation_scalar, tensorModelTransformation_scalar]
  exact onFunctor_whisker_square _ _ _ _ (tensorSupportedRawModelInputIso p q a b h).hom
    (smallUnit (X := op A.obj.right) A.obj.hom r)
    (smallUnit (X := op C.obj.right) C.obj.hom
      (Units.map a.hom.right.appTop.hom.toMonoidHom r))
    (evaluationRawMap_preserves a r).whisker

end Quillen.PerfectComplexes.SupportedTensorEvaluation
