/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelInputEdges
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedNormalizedEvaluationInputSquare
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteRectangle

/-! # The complete actual supported tensor Model input rectangle

For every original commutative pair square, evaluation of the independently constructed raw
tensor square agrees with the two genuine Model evaluation routes. Every original supported
transition, tensor unitor, selected-zero rebase, and functor associator is retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation evaluationNormalizationIso
  internalTensorModelIso evaluationComparisonIso supportedTensorCoefficientNormalization
  evaluationRawNormalization
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The original tensor comparison followed by the original geometric evaluation edge. -/
def modelEvaluationInputLeft :=
  (isoSquareRoute (internalTensorModelIso p) (evaluationComparisonIso a)).symm

/-- The original geometric evaluation edge followed by the target tensor comparison. -/
def modelEvaluationInputRight :=
  (isoSquareRoute (evaluationComparisonIso b) (internalTensorModelIso q)).symm

/-- Actual evaluation of the independent supported raw Model tensor input square. -/
def rawEvaluatedInputIso :=
  isoWhiskerLeft (evaluationModel (X := op B.obj.right) B.obj.hom).functor
    (tensorSupportedRawModelInputIso p q a b h)

private def leftCoefficientRoute :=
  isoSquareRoute (supportedSmallCoefficientIso p (supportedTensorCoefficientNormalization p))
    (supportedSmallCoefficientIso a (evaluationRawNormalization a))

private def rightCoefficientRoute :=
  isoSquareRoute (supportedSmallCoefficientIso b (evaluationRawNormalization b))
    (supportedSmallCoefficientIso q (supportedTensorCoefficientNormalization q))

private theorem leftRoute_normalized :
    modelEvaluationInputLeft p a =
      (isoSquareConjugate (leftCoefficientRoute p a)
        (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
        (evaluationNormalizationIso (X := op C.obj.right) C.obj.hom)).symm := by
  unfold modelEvaluationInputLeft
  rw [internalTensorModelIso_smallCoefficient, evaluationComparisonIso_smallCoefficient]
  apply congrArg Iso.symm
  exact isoSquareRoute_conjugate _ _ _ _ _

private theorem rightRoute_normalized :
    modelEvaluationInputRight q b =
      (isoSquareConjugate (rightCoefficientRoute q b)
        (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
        (evaluationNormalizationIso (X := op C.obj.right) C.obj.hom)).symm := by
  unfold modelEvaluationInputRight
  rw [internalTensorModelIso_smallCoefficient, evaluationComparisonIso_smallCoefficient]
  apply congrArg Iso.symm
  exact isoSquareRoute_conjugate _ _ _ _ _

/-- The complete supported Model rectangle retains its actual raw tensor comparison. -/
theorem modelEvaluationInputRectangle_hom :
    (rawEvaluatedInputIso p q a b h).hom ≫ (modelEvaluationInputRight q b).hom =
      (modelEvaluationInputLeft p a).hom ≫
        eqToHom (congrArg (fun F => F ⋙
          (evaluationModel (X := op C.obj.right) C.obj.hom).functor)
          (supportedReindexInputSquare p q a b h)) := by
  have hs := isoSquareConjugate_rectangle
    (isoSquareRoute
      (supportedSmallCoefficientIso p (supportedTensorCoefficientNormalization p))
      (supportedSmallCoefficientIso a (evaluationRawNormalization a)))
    (isoSquareRoute
      (supportedSmallCoefficientIso b (evaluationRawNormalization b))
      (supportedSmallCoefficientIso q (supportedTensorCoefficientNormalization q)))
    (supportedSmallInputSquareIso p q a b h
      (supportedTensorCoefficientNormalization p) (evaluationRawNormalization a)
      (evaluationRawNormalization b) (supportedTensorCoefficientNormalization q))
    (supportedReindexInputSquare p q a b h)
    (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
    (evaluationNormalizationIso (X := op C.obj.right) C.obj.hom)
    (supportedSmallInputSquare_hom p q a b h
      (supportedTensorCoefficientNormalization p) (evaluationRawNormalization a)
      (evaluationRawNormalization b) (supportedTensorCoefficientNormalization q))
  rw [leftRoute_normalized, rightRoute_normalized]
  unfold rawEvaluatedInputIso
  rw [tensorSupportedRawModelInputIso_eq]
  exact hs

attribute [local irreducible] rawEvaluatedInputIso
  modelEvaluationInputLeft modelEvaluationInputRight

/-- Equality of the actual full isomorphisms, retaining the original supported reindex transport. -/
theorem modelEvaluationInputRectangle :
    rawEvaluatedInputIso p q a b h ≪≫ modelEvaluationInputRight q b =
      modelEvaluationInputLeft p a ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (evaluationModel (X := op C.obj.right) C.obj.hom).functor)
          (supportedReindexInputSquare p q a b h)) :=
  Iso.ext (modelEvaluationInputRectangle_hom p q a b h)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
