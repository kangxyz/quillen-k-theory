/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationModel
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence

/-! # The exact inverse of original supported evaluation

The categorical inverse retains the original support predicate and the actual transported
Waldhausen structure. Its chosen zero is normalized with the original unit and counit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The original supported equivalence followed by common-universe transport. -/
def evaluationSmallEquivalence :
    supportedModel j ≌ SmallModel ((boundedFlatPerfectSupported j).FullSubcategory) :=
  (supportedEvaluation j).asEquivalence.trans AsSmall.equiv

/-- The actual inverse is exact for the original supported classes. -/
theorem evaluationSmallEquivalence_inverse_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen j).smallModel.cof
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.weq
      (supportedModel j).waldhausen.cof (supportedModel j).waldhausen.weq
      (evaluationSmallEquivalence j).inverse :=
  (boundedFlatPerfectSupportedWaldhausen j).smallModel_down_exact.comp
    (Structure.ofEquivalence_inverse_exact _ _ _ (supportedZero_evaluation_isZero j))

/-- The forward functor is exactly the accepted normalized supported evaluation. -/
def evaluationModelEquivalence :
    supportedModel j ≌ modelOf (boundedFlatPerfectSupportedWaldhausen j) :=
  (evaluationSmallEquivalence j).changeFunctor (evaluationNormalizationIso j)

/-- The genuine categorical inverse, normalized at the original chosen zero. -/
def evaluationInverseModel :
    modelOf (boundedFlatPerfectSupportedWaldhausen j) ⟶ supportedModel j :=
  ExactModelEquivalence.backward (evaluationModelEquivalence j)
    (evaluationSmallEquivalence_inverse_exact j)

/-- The original unit with its complete chosen-zero normalization. -/
def evaluationInverseUnit :
    (evaluationModel j ≫ evaluationInverseModel j).functor ≅
      (𝟙 (supportedModel j) : supportedModel j ⟶ supportedModel j).functor :=
  ExactModelEquivalence.unitIso (evaluationModelEquivalence j) (evaluationModel j).exact
    (evaluationSmallEquivalence_inverse_exact j) (evaluationModel j).zero

/-- The original counit with the same actual inverse. -/
def evaluationInverseCounit :
    (evaluationInverseModel j ≫ evaluationModel j).functor ≅
      (𝟙 (modelOf (boundedFlatPerfectSupportedWaldhausen j)) :
        modelOf (boundedFlatPerfectSupportedWaldhausen j) ⟶
          modelOf (boundedFlatPerfectSupportedWaldhausen j)).functor :=
  ExactModelEquivalence.counitIso (evaluationModelEquivalence j) (evaluationModel j).exact
    (evaluationSmallEquivalence_inverse_exact j) (evaluationModel j).zero

end Quillen.PerfectComplexes.SupportedTensorEvaluation
