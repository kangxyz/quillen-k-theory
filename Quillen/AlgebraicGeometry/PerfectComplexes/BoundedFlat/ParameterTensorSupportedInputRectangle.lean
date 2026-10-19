/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelInputRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedInput

/-! # The actual supported tensor input rectangle at every scheme parameter

The parameter arrow is arbitrary. Its genuine product-pair square supplies the raw tensor
comparison, and the complete evaluated rectangle retains all original supported Model edges.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass.GeometricSeedCospan
universe u
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex SupportedTensorEvaluation
attribute [local irreducible] globalModel globalEvaluation GlobalSupportedParameter.pairMap
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
  {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)

/-- The genuine product-pair input map at an arbitrary parameter arrow. -/
def inputPair : pair f Y ⟶ pair f X := GlobalSupportedParameter.pairMap f g.unop

private theorem mapSquare {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {W X Y Z : C} (p : X ⟶ W) (q : Z ⟶ Y)
    (a : Z ⟶ X) (b : Y ⟶ W) (h : a ≫ p = q ≫ b) :
    F.map a ≫ F.map p = F.map q ≫ F.map b := by
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map h

/-- The original Laurent coefficient and product-pair input form the complete pair square. -/
theorem coefficientPair_input :
    inputPair f (laurent.op.map g) ≫ coefficientPair f X =
      coefficientPair f Y ≫ inputPair f g :=
  mapSquare (GlobalSupportedParameter.pairs f) (coefficient.app X).unop
    (coefficient.app Y).unop (laurent.op.map g).unop g.unop
    (congrArg Quiver.Hom.unop (coefficient.naturality g).symm)

/-- Actual supported tensor evaluation commutes on every original scheme parameter input. -/
theorem inputRectangle :
    rawEvaluatedInputIso (coefficientPair f X) (coefficientPair f Y)
        (inputPair f (laurent.op.map g)) (inputPair f g) (coefficientPair_input f g) ≪≫
        modelEvaluationInputRight (coefficientPair f Y) (inputPair f g) =
      modelEvaluationInputLeft (coefficientPair f X) (inputPair f (laurent.op.map g)) ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (evaluationModel (X := op (pair f (laurent.op.obj Y)).obj.right)
            (pair f (laurent.op.obj Y)).obj.hom).functor)
          (supportedReindexInputSquare (coefficientPair f X) (coefficientPair f Y)
            (inputPair f (laurent.op.map g)) (inputPair f g) (coefficientPair_input f g))) :=
  modelEvaluationInputRectangle _ _ _ _ _

private theorem whiskerRight_transport {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (h : F = G) (J : D ⥤ E) :
    whiskerRight (eqToHom h) J = eqToHom (congrArg (fun K => K ⋙ J) h) := by
  subst G
  simp

/-- The original parameter coefficient square keeps its literal supported source transport. -/
theorem coefficientFunctorSquare_evaluation :
    isoWhiskerRight
        (ParameterTensorEvaluationRow.coefficientFunctorSquare (ParameterModels.supported f) g)
        (evaluationModel (X := op (pair f (laurent.op.obj Y)).obj.right)
          (pair f (laurent.op.obj Y)).obj.hom).functor =
      eqToIso (congrArg (fun F => F ⋙
        (evaluationModel (X := op (pair f (laurent.op.obj Y)).obj.right)
          (pair f (laurent.op.obj Y)).obj.hom).functor)
        (supportedReindexInputSquare (coefficientPair f X) (coefficientPair f Y)
          (inputPair f (laurent.op.map g)) (inputPair f g) (coefficientPair_input f g))) := by
  apply Iso.ext
  simp only [ParameterTensorEvaluationRow.coefficientFunctorSquare, isoWhiskerRight_hom,
    eqToIso.hom, whiskerRight_transport]

attribute [local irreducible] rawEvaluatedInputIso
  modelEvaluationInputLeft modelEvaluationInputRight

/-- The whole genuine tensor rectangle recovers the original supported parameter input square. -/
theorem modelEvaluationInputSquare :
    modelEvaluationInputLeft (coefficientPair f X) (inputPair f (laurent.op.map g)) ≪≫
        isoWhiskerRight
          (ParameterTensorEvaluationRow.coefficientFunctorSquare (ParameterModels.supported f) g)
          (evaluationModel (X := op (pair f (laurent.op.obj Y)).obj.right)
            (pair f (laurent.op.obj Y)).obj.hom).functor =
      rawEvaluatedInputIso (coefficientPair f X) (coefficientPair f Y)
        (inputPair f (laurent.op.map g)) (inputPair f g) (coefficientPair_input f g) ≪≫
        modelEvaluationInputRight (coefficientPair f Y) (inputPair f g) := by
  rw [coefficientFunctorSquare_evaluation]
  exact (inputRectangle f g).symm

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
