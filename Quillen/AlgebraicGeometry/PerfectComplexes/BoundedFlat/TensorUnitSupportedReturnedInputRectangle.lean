/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelInputRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedReturnedCounit
public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareRouteWhiskering

/-! # Original returned tensor input in supported categories

The genuine return counit identifies the entire returned input route with the independently
specified supported raw tensor square. All four pair arrows and the original strict section
transport are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The original supported input square conjugated by its genuine tensor return isomorphisms. -/
def returnedInputIso :=
  isoWhiskerRight (returnedTensorIso p).symm (supportedPairModelMap a).functor ≪≫
    eqToIso (supportedReindexInputSquare p q a b h) ≪≫
      isoWhiskerLeft (supportedPairModelMap b).functor (returnedTensorIso q)

/-- Tensor first, retaining the specified supported evaluation counit. -/
def returnedEvaluationInputLeft :=
  (isoSquareRoute (returnedTensorEvaluationIso p) (evaluationComparisonIso a)).symm

/-- Input first, retaining the specified supported evaluation counit. -/
def returnedEvaluationInputRight :=
  (isoSquareRoute (evaluationComparisonIso b) (returnedTensorEvaluationIso q)).symm

/-- The whole original supported tensor movement is recovered after return and evaluation. -/
theorem returnedTensorIso_evaluation_iso :
    isoWhiskerRight (returnedTensorIso p)
        (evaluationModel (X := op A.obj.right) A.obj.hom).functor ≪≫
      returnedTensorEvaluationIso p = internalTensorModelIso p :=
  Iso.ext (returnedTensorIso_evaluation p)

/-- The left route keeps the entire returned input movement. -/
theorem returnedEvaluationInputLeft_eq :
    returnedEvaluationInputLeft p a = modelEvaluationInputLeft p a ≪≫
      isoWhiskerRight
        (isoWhiskerRight (returnedTensorIso p) (supportedPairModelMap a).functor)
        (evaluationModel (X := op C.obj.right) C.obj.hom).functor := by
  unfold modelEvaluationInputLeft
  rw [← returnedTensorIso_evaluation_iso, isoSquareRoute_leftIso, Iso.trans_symm]
  simp only [returnedEvaluationInputLeft, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- The right route keeps the actual input whiskering of the return movement. -/
theorem returnedEvaluationInputRight_eq :
    returnedEvaluationInputRight q b = modelEvaluationInputRight q b ≪≫
      isoWhiskerRight
        (isoWhiskerLeft (supportedPairModelMap b).functor (returnedTensorIso q))
        (evaluationModel (X := op C.obj.right) C.obj.hom).functor := by
  unfold modelEvaluationInputRight
  rw [← returnedTensorIso_evaluation_iso, isoSquareRoute_rightIso, Iso.trans_symm]
  simp only [returnedEvaluationInputRight, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

private theorem whiskerEquality {V W Z : Type*} [Category V] [Category W] [Category Z]
    {F G : V ⥤ W} (e : F = G) (E : W ⥤ Z) :
    isoWhiskerRight (eqToIso e) E = eqToIso (congrArg (fun F => F ⋙ E) e) := by
  subst G
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact E.map_id (F.obj X)

private theorem returnedRectangle {V : Type*} [Category V]
    {A B C D A' B' : V} (r : A ≅ B) (l : A ≅ C) (t : B ≅ D)
    (s : C ≅ D) (a : C ≅ A') (b : D ≅ B')
    (h : r ≪≫ t = l ≪≫ s) :
    r ≪≫ (t ≪≫ b) = (l ≪≫ a) ≪≫ (a.symm ≪≫ s ≪≫ b) := by
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc] using
    congrArg (fun k => k ≪≫ b) h

/-- The actual supported raw input square is recovered by the specified forward evaluation. -/
theorem returnedInputIso_evaluation_rectangle :
    rawEvaluatedInputIso p q a b h ≪≫ returnedEvaluationInputRight q b =
      returnedEvaluationInputLeft p a ≪≫
        isoWhiskerRight (returnedInputIso p q a b h)
          (evaluationModel (X := op C.obj.right) C.obj.hom).functor := by
  rw [returnedEvaluationInputLeft_eq, returnedEvaluationInputRight_eq]
  unfold returnedInputIso
  rw [isoWhiskerRight_trans, isoWhiskerRight_trans]
  simp only [whiskerEquality]
  exact returnedRectangle _ _ _ _ _ _ (modelEvaluationInputRectangle p q a b h)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
