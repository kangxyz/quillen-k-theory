/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedModels
public import Quillen.Waldhausen.SmallModel.Whiskering

/-!
# Original chosen-zero evaluation of supported sections

The actual supported evaluation is first placed in the original common universe. Only its
chosen zero is normalized, with the complete original comparison isomorphism retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- Evaluation in the original common universe, with the actual supported predicate. -/
def evaluationSmall :
    supportedModel j ⥤ SmallModel ((boundedFlatPerfectSupported j).FullSubcategory) :=
  supportedEvaluation j ⋙ AsSmall.up

/-- The original supported evaluation is exact after universe transport. -/
theorem evaluationSmall_exact :
    IsExact (supportedModel j).waldhausen.cof (supportedModel j).waldhausen.weq
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.cof
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.weq (evaluationSmall j) :=
  (supportedEvaluation_exact j).comp
    (boundedFlatPerfectSupportedWaldhausen j).smallModel_up_exact

/-- The evaluated original chosen zero has its unique actual zero comparison. -/
def evaluationZeroIso :
    (evaluationSmall j).obj (supportedModel j).waldhausen.zero ≅
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.zero :=
  ((evaluationSmall_exact j).zero (supportedModel j).waldhausen.isZero).iso
    (boundedFlatPerfectSupportedWaldhausen j).smallModel.isZero

/-- The actual supported evaluation as a chosen-zero Model map. -/
def evaluationModel : supportedModel j ⟶ modelOf (boundedFlatPerfectSupportedWaldhausen j) where
  functor := Quillen.rebaseFunctor (evaluationSmall j) (supportedModel j).waldhausen.zero
    (boundedFlatPerfectSupportedWaldhausen j).smallModel.zero (evaluationZeroIso j)
  exact := (evaluationSmall_exact j).rebase
  zero := Quillen.rebaseFunctor_obj_base _ _ _ _

/-- The whole original chosen-zero normalization isomorphism. -/
def evaluationNormalizationIso : evaluationSmall j ≅ (evaluationModel j).functor :=
  Quillen.rebaseFunctorIso _ _ _ (evaluationZeroIso j)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
