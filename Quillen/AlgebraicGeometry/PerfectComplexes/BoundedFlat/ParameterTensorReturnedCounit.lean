/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedModel

/-!
# Forward evaluation recovers the original genuine tensor action

The actual categorical counit identifies the returned tensor functor followed by
forward evaluation with the unchanged raw tensor functor. Its full naturality
square preserves the original tensor multiplication, rather than only its class.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- The specified categorical counit after an arbitrary actual input functor. -/
def returnCounit {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C ⥤ E) (B : E ⥤ D) (A : D ⥤ E) (j : B ⋙ A ≅ 𝟭 E) :
    (T ⋙ B) ⋙ A ≅ T :=
  Functor.associator T B A ≪≫ isoWhiskerLeft T j ≪≫ Functor.rightUnitor T

/-- The counit intertwines the entire transported transformation with its original value. -/
theorem returnCounit_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C ⥤ E) (B : E ⥤ D) (A : D ⥤ E) (j : B ⋙ A ≅ 𝟭 E) (η : T ⟶ T) :
    whiskerRight (whiskerRight η B) A ≫ (returnCounit T B A j).hom =
      (returnCounit T B A j).hom ≫ η := by
  apply NatTrans.ext
  funext X
  simpa [returnCounit] using j.hom.naturality (η.app X)

/-- Forward evaluation of the returned tensor map recovers the original raw tensor Model map.
-/
def returnedTensorEvaluationIso (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (returnedTensorModel Q X ≫ evaluationModel (op (scheme Q (laurent.op.obj X)))).functor ≅
      (tensorModelMap Q X).functor :=
  returnCounit (tensorModelMap Q X).functor
    (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))).functor
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor
    (evaluationInverseCounit (op (scheme Q (laurent.op.obj X))))

/-- The counit preserves the entire original tensor multiplication transformation. -/
theorem returnedTensorEvaluationIso_unit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    whiskerRight (returnedTensorUnit Q X)
      (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor ≫
      (returnedTensorEvaluationIso Q X).hom =
    (returnedTensorEvaluationIso Q X).hom ≫ tensorModelUnit Q X :=
  returnCounit_unit _ _ _ _ _

/-- The actual forward counit supplies the complete genuine tensor first-row comparison prism.
-/
def returnedTensorEvaluationPasting (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  rowTransformationPasting
    (F := returnedTensorModel Q X ≫ evaluationModel (op (scheme Q (laurent.op.obj X))))
    (G := returnedTensorModel Q X ≫ evaluationModel (op (scheme Q (laurent.op.obj X))))
    (G' := tensorModelMap Q X) (H := tensorModelMap Q X)
    (whiskerRight (returnedTensorUnit Q X)
      (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor)
    (returnedTensorEvaluationIso Q X).hom (returnedTensorEvaluationIso Q X).hom
    (tensorModelUnit Q X)
    (fun A => (evaluationModel (op (scheme Q (laurent.op.obj X)))).exact.weak _
      ((evaluationInverseModel (op (scheme Q (laurent.op.obj X)))).exact.weak _
        (tensorModelUnit_weak Q X A)))
    (fun _ => (modelOf (boundedFlatPerfectWaldhausen
      (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _ inferInstance)
    (fun _ => (modelOf (boundedFlatPerfectWaldhausen
      (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _ inferInstance)
    (tensorModelUnit_weak Q X) (returnedTensorEvaluationIso_unit Q X)

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
