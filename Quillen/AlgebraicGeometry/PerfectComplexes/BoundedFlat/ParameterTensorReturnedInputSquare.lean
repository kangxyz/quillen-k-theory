/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorModelInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedTriangle
public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareRouteWhiskering

/-! # The specified returned tensor input square under genuine evaluation

Both routes use the actual return counit and original geometric evaluation comparisons.
Their common raw side is independently constructed from the tensor unitors and geometric
pullback composition, with its original zero normalizations.
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
variable (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)

/-- Tensor first, with the specified forward evaluation counit and original input comparison. -/
def returnedEvaluationInputLeft :=
  (isoSquareRoute (returnedTensorEvaluationIso Q X)
    (evaluationComparisonIso (inputSchemeMap Q (laurent.op.map g)))).symm

/-- Input first, with the original input comparison and specified forward evaluation counit. -/
def returnedEvaluationInputRight :=
  (isoSquareRoute (evaluationComparisonIso (inputSchemeMap Q g))
    (returnedTensorEvaluationIso Q Y)).symm

/-- The specified original Model movement is recovered as an equality of entire isomorphisms. -/
theorem returnedTensorIso_evaluation_iso (X : Scheme.{u}ᵒᵖ) :
    isoWhiskerRight (returnedTensorIso Q X)
        (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor ≪≫
      returnedTensorEvaluationIso Q X = internalTensorModelIso Q X := by
  apply Iso.ext
  exact returnedTensorIso_evaluation Q X

/-- The actual returned first route is the original route followed by its specified return iso. -/
theorem returnedEvaluationInputLeft_eq :
    returnedEvaluationInputLeft Q g = modelEvaluationInputLeft Q g ≪≫
      isoWhiskerRight
        (isoWhiskerRight (returnedTensorIso Q X)
          (globalModel.map (inputSchemeMap Q (laurent.op.map g)).op).functor)
        (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor := by
  rw [modelEvaluationInputLeft_route, ← returnedTensorIso_evaluation_iso,
    isoSquareRoute_leftIso, Iso.trans_symm]
  simp only [returnedEvaluationInputLeft, Iso.trans_assoc, Iso.symm_self_id,
    Iso.trans_refl]

/-- The actual returned second route retains the input whiskering of the specified return iso. -/
theorem returnedEvaluationInputRight_eq :
    returnedEvaluationInputRight Q g = modelEvaluationInputRight Q g ≪≫
      isoWhiskerRight
        (isoWhiskerLeft (globalModel.map (inputSchemeMap Q g).op).functor
          (returnedTensorIso Q Y))
        (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor := by
  rw [modelEvaluationInputRight_route, ← returnedTensorIso_evaluation_iso,
    isoSquareRoute_rightIso, Iso.trans_symm]
  simp only [returnedEvaluationInputRight, Iso.trans_assoc, Iso.symm_self_id,
    Iso.trans_refl]

private theorem returnedRectangle {C : Type*} [Category C]
    {A B C₀ D A' B' : C} (r : A ≅ B) (l : A ≅ C₀) (t : B ≅ D)
    (s : C₀ ≅ D) (a : C₀ ≅ A') (b : D ≅ B')
    (h : r ≪≫ t = l ≪≫ s) :
    r ≪≫ (t ≪≫ b) = (l ≪≫ a) ≪≫ (a.symm ≪≫ s ≪≫ b) := by
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc] using
    congrArg (fun k => k ≪≫ b) h

/-- Evaluation of the specified return square retains its complete conjugation word. -/
theorem returnedInputIso_evaluation_word :
    isoWhiskerRight (returnedInputIso Q g)
        (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor =
      (isoWhiskerRight (isoWhiskerRight (returnedTensorIso Q X)
        (globalModel.map (inputSchemeMap Q (laurent.op.map g)).op).functor)
        (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor).symm ≪≫
      isoWhiskerRight (coefficientFunctorSquare (ParameterModels.ambient Q) g)
        (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor ≪≫
      isoWhiskerRight (isoWhiskerLeft (globalModel.map (inputSchemeMap Q g).op).functor
        (returnedTensorIso Q Y))
        (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor := by
  unfold returnedInputIso
  rw [isoWhiskerRight_trans, isoWhiskerRight_trans,
    isoWhiskerRight_symm, isoWhiskerRight_symm]
  rfl

/-- Forward evaluation identifies the returned input with the independently specified raw square.
-/
theorem returnedInputIso_evaluation_square :
    rawEvaluatedInputIso Q g ≪≫ returnedEvaluationInputRight Q g =
      returnedEvaluationInputLeft Q g ≪≫
        isoWhiskerRight (returnedInputIso Q g)
          (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor := by
  rw [returnedEvaluationInputLeft_eq, returnedEvaluationInputRight_eq,
    returnedInputIso_evaluation_word]
  exact returnedRectangle _ _ _ _ _ _ (modelEvaluationInputSquare Q g).symm

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
