/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackForgetComparison

/-! # Original supported input components in the ambient category

These component identities retain the genuine supported pullback and evaluation maps while
presenting their endpoints in the original ambient category. They isolate object normalization
from the complete arbitrary supported input rectangle.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation
  evaluationPullbackIso supportedPairReindexEvaluationIso
variable {A B C : Scheme.OpenPairs.{u}} (f : A ⟶ B) (g : B ⟶ C)
  (K : (supported (X := op C.obj.right) C.obj.hom).FullSubcategory)

/-- The actual supported forward composition component at an evaluated original section. -/
theorem supportedEvaluationComp_forget_hom_app :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((boundedFlatPerfectSupportedPullbackCompIso f g).hom.app
          ((supportedEvaluation (X := op C.obj.right) C.obj.hom).obj K)) =
      (boundedFlatPerfectPullbackCompIso f.hom.right g.hom.right).hom.app
        ((globalEvaluation (op C.obj.right)).obj K.obj) :=
  boundedFlatPerfectSupportedPullbackCompIso_forget_hom_app f g _

/-- The actual supported inverse composition component at an evaluated original section. -/
theorem supportedEvaluationComp_forget_inv_app :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((boundedFlatPerfectSupportedPullbackCompIso f g).inv.app
          ((supportedEvaluation (X := op C.obj.right) C.obj.hom).obj K)) =
      (boundedFlatPerfectPullbackCompIso f.hom.right g.hom.right).inv.app
        ((globalEvaluation (op C.obj.right)).obj K.obj) :=
  boundedFlatPerfectSupportedPullbackCompIso_forget_inv_app f g _

/-- The original supported evaluation component after an actual pair reindexing. -/
theorem supportedReindexEvaluation_forget_hom_app :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((supportedPairReindexEvaluationIso f).hom.app ((supportedPairReindex g).obj K)) =
      (evaluationPullbackIso f.hom.right).hom.app
        ((globalModel.map g.hom.right.op).functor.obj K.obj) :=
  supportedPairReindexEvaluationIso_forget_hom_app f _

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
