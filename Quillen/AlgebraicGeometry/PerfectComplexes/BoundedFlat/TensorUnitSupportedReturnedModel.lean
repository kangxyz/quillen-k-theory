/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInverseModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRowPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedModel

/-! # Returning the genuine supported tensor through its actual evaluation equivalence

The original supported tensor functor and multiplication pass through the exact categorical
inverse. The original unit supplies the moving endpoint; no supported spectral faithfulness
is used to infer this comparison.
-/
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

/-- Return the genuine supported tensor to the original supported section Model. -/
def returnedTensorModel :=
  tensorModelMap p ≫ evaluationInverseModel (X := op A.obj.right) A.obj.hom

/-- The specified evaluation unit and genuine tensor unitor give the moving endpoint. -/
def returnedTensorIso :
    (supportedPairModelMap p).functor ≅ (returnedTensorModel p).functor :=
  ParameterTensorEvaluationRow.returnIso (supportedPairModelMap p).functor
    (evaluationModel (X := op A.obj.right) A.obj.hom).functor
    (evaluationInverseModel (X := op A.obj.right) A.obj.hom).functor
    (tensorModelMap p).functor
    (evaluationInverseUnit (X := op A.obj.right) A.obj.hom) (internalTensorModelIso p)

/-- The actual tensor multiplication is transported by the exact inverse functor. -/
def returnedTensorUnit :=
  whiskerRight (tensorModelUnit p r)
    (evaluationInverseModel (X := op A.obj.right) A.obj.hom).functor

/-- The entire internal unit and genuine returned multiplication satisfy the original square. -/
theorem returnedTensorIso_unit :
    (onFunctor (supportedPairModelMap p).functor
      (unit (X := op A.obj.right) A.obj.hom r)).hom ≫ (returnedTensorIso p).hom =
        (returnedTensorIso p).hom ≫ returnedTensorUnit p r :=
  ParameterTensorEvaluationRow.returnIso_intertwining _ _ _ _ _ _ _ _
    (internalTensorModelIso_unit p r)

/-- The original supported weak multiplication remains weak after exact return. -/
theorem returnedTensorUnit_weak
    (K : supportedModel (X := op B.obj.right) B.obj.hom) :
    (supportedModel (X := op A.obj.right) A.obj.hom).waldhausen.weq
      ((returnedTensorUnit p r).app K) :=
  (evaluationInverseModel (X := op A.obj.right) A.obj.hom).exact.weak _
    (tensorModelUnit_weak p r K)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
