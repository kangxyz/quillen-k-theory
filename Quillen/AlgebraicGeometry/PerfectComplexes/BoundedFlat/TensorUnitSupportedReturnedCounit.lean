/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedReturnedCell
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedTriangle

/-! # The supported return retains its genuine tensor provenance

Forward evaluation of the returned action is identified with the original supported tensor
by the specified categorical counit. The whole multiplication square induces the actual
first-row prism, preserving both independent times and the zero-level input loop.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.obj.right, ⊤))ˣ)

/-- The actual supported categorical counit recovers the unchanged raw tensor Model functor. -/
def returnedTensorEvaluationIso :
    (returnedTensorModel p ≫ evaluationModel (X := op A.obj.right) A.obj.hom).functor ≅
      (tensorModelMap p).functor :=
  ParameterTensorEvaluationRow.returnCounit (tensorModelMap p).functor
    (evaluationInverseModel (X := op A.obj.right) A.obj.hom).functor
    (evaluationModel (X := op A.obj.right) A.obj.hom).functor
    (evaluationInverseCounit (X := op A.obj.right) A.obj.hom)

/-- Reevaluating the returned supported movement recovers the specified original tensor unitor. -/
theorem returnedTensorIso_evaluation :
    whiskerRight (returnedTensorIso p).hom
        (evaluationModel (X := op A.obj.right) A.obj.hom).functor ≫
      (returnedTensorEvaluationIso p).hom = (internalTensorModelIso p).hom :=
  ParameterTensorEvaluationRow.returnIso_counit_exact
    (evaluationModelEquivalence (X := op A.obj.right) A.obj.hom)
    (evaluationModel (X := op A.obj.right) A.obj.hom).exact
    (evaluationSmallEquivalence_inverse_exact (X := op A.obj.right) A.obj.hom)
    (evaluationModel (X := op A.obj.right) A.obj.hom).zero
    (supportedPairModelMap p).functor (tensorModelMap p).functor (internalTensorModelIso p)

/-- The entire original supported tensor multiplication is preserved by that counit. -/
theorem returnedTensorEvaluationIso_unit :
    whiskerRight (returnedTensorUnit p r)
      (evaluationModel (X := op A.obj.right) A.obj.hom).functor ≫
        (returnedTensorEvaluationIso p).hom =
      (returnedTensorEvaluationIso p).hom ≫ tensorModelUnit p r :=
  ParameterTensorEvaluationRow.returnCounit_unit _ _ _ _ _

/-- Forward exact evaluation preserves every original returned tensor time and row coordinate. -/
theorem returnedTensorEvaluationCell_at (t : unitInterval) :
    (rowTransformationSpectrumHomotopy
      (F := returnedTensorModel p ≫ evaluationModel (X := op A.obj.right) A.obj.hom)
      (G := returnedTensorModel p ≫ evaluationModel (X := op A.obj.right) A.obj.hom)
      (whiskerRight (returnedTensorUnit p r)
        (evaluationModel (X := op A.obj.right) A.obj.hom).functor)
      (fun K => (evaluationModel (X := op A.obj.right) A.obj.hom).exact.weak _
        (returnedTensorUnit_weak p r K))).at t =
      (returnedTensorCell p r).at t ≫
        rowLoopMap (evaluationModel (X := op A.obj.right) A.obj.hom) :=
  rowTransformationSpectrumHomotopy_postcomp_at
    (F := returnedTensorModel p) (G := returnedTensorModel p) (returnedTensorUnit p r)
    (returnedTensorUnit_weak p r) (evaluationModel (X := op A.obj.right) A.obj.hom) t

/-- The counit gives the genuine supported tensor first-row comparison, with moving endpoints.
-/
def returnedTensorEvaluationPasting :=
  rowTransformationPasting
    (F := returnedTensorModel p ≫ evaluationModel (X := op A.obj.right) A.obj.hom)
    (G := returnedTensorModel p ≫ evaluationModel (X := op A.obj.right) A.obj.hom)
    (G' := tensorModelMap p) (H := tensorModelMap p)
    (whiskerRight (returnedTensorUnit p r)
      (evaluationModel (X := op A.obj.right) A.obj.hom).functor)
    (returnedTensorEvaluationIso p).hom (returnedTensorEvaluationIso p).hom
    (tensorModelUnit p r)
    (fun K => (evaluationModel (X := op A.obj.right) A.obj.hom).exact.weak _
      (returnedTensorUnit_weak p r K))
    (fun _ => (modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom)).waldhausen.weq_iso
      _ inferInstance)
    (fun _ => (modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom)).waldhausen.weq_iso
      _ inferInstance)
    (tensorModelUnit_weak p r) (returnedTensorEvaluationIso_unit p r)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
