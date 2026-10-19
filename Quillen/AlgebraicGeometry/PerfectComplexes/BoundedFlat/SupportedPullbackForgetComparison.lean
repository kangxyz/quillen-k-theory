/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedPairNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairModel

/-! # Actual supported geometric comparisons after forgetting support

The original pullback composition and evaluation comparisons retain their original ambient
morphisms under the genuine inclusion of supported full subcategories. These formulas concern
natural transformations before normalization or realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {A B C : Scheme.OpenPairs.{u}}

/-- Genuine supported pullback and the ambient pullback have the same underlying map. -/
theorem boundedFlatPerfectSupportedPullback_forget_map (p : A ⟶ B)
    {K L : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory} (k : K ⟶ L) :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((boundedFlatPerfectSupportedPullback p).map k) =
      (boundedFlatPerfectPullback p.hom.right).map
        ((tensorCoefficientSupportedForget B.obj.hom).map k) := rfl

/-- The actual supported composition edge has the original ambient forward component. -/
theorem boundedFlatPerfectSupportedPullbackCompIso_forget_hom_app
    (f : A ⟶ B) (g : B ⟶ C)
    (K : (boundedFlatPerfectSupported C.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((boundedFlatPerfectSupportedPullbackCompIso f g).hom.app K) =
      (boundedFlatPerfectPullbackCompIso f.hom.right g.hom.right).hom.app
        ((tensorCoefficientSupportedForget C.obj.hom).obj K) := by
  apply (boundedFlatPerfect A.obj.right).ι.map_injective
  change (boundedFlatPerfectSupported A.obj.hom).ι.map
      ((boundedFlatPerfectSupportedPullbackCompIso f g).hom.app K) = _
  simp only [boundedFlatPerfectSupportedPullbackCompIso, boundedFlatPerfectPullbackCompIso,
    fullyFaithfulCancelRight_hom_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.map_preimage]
  rfl

/-- The inverse actual supported composition edge retains the original ambient inverse. -/
theorem boundedFlatPerfectSupportedPullbackCompIso_forget_inv_app
    (f : A ⟶ B) (g : B ⟶ C)
    (K : (boundedFlatPerfectSupported C.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((boundedFlatPerfectSupportedPullbackCompIso f g).inv.app K) =
      (boundedFlatPerfectPullbackCompIso f.hom.right g.hom.right).inv.app
        ((tensorCoefficientSupportedForget C.obj.hom).obj K) := by
  apply (boundedFlatPerfect A.obj.right).ι.map_injective
  change (boundedFlatPerfectSupported A.obj.hom).ι.map
      ((boundedFlatPerfectSupportedPullbackCompIso f g).inv.app K) = _
  simp only [boundedFlatPerfectSupportedPullbackCompIso, boundedFlatPerfectPullbackCompIso,
    fullyFaithfulCancelRight_inv_app, isoWhiskerLeft_inv, whiskerLeft_app,
    Functor.map_preimage]
  rfl

namespace GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation

/-- The original evaluated component is unchanged by forgetting support. -/
theorem supportedPairReindexEvaluationIso_forget_hom_app (p : A ⟶ B)
    (K : (supported (X := Opposite.op B.obj.right) B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((supportedPairReindexEvaluationIso p).hom.app K) =
      (evaluationPullbackIso p.hom.right).hom.app K.obj := by
  apply (boundedFlatPerfect A.obj.right).ι.map_injective
  change (boundedFlatPerfectSupported A.obj.hom).ι.map
      ((supportedPairReindexEvaluationIso p).hom.app K) = _
  simp only [supportedPairReindexEvaluationIso, fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, ObjectProperty.ι_obj]

end GlobalSectionChangeIndex

end Quillen.PerfectComplexes
