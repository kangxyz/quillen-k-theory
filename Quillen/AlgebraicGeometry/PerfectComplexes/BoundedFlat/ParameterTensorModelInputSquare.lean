/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorModelInputEdges
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteRectangle

/-! # The genuine tensor Model evaluation square at every parameter input

This rectangle identifies the independently defined raw tensor square with the original
strict parameter coefficient square, through the specified evaluation and tensor movement
isomorphisms. Both raw and evaluation chosen-zero normalizations are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.CategoryTheory.GrothendieckSections
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w v₁ w₁
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex
attribute [local irreducible] evaluationNormalizationIso internalTensorModelIso
  evaluationComparisonIso tensorCoefficientNormalization evaluationRawNormalization

variable (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)

private def leftCoefficientRoute :=
  smallCoefficientRouteIso boundedFlatPerfectPseudofunctor
    (coefficientMap Q X).op (inputSchemeMap Q (laurent.op.map g)).op
    (tensorCoefficientNormalization (coefficientMap Q X))
    (evaluationRawNormalization (inputSchemeMap Q (laurent.op.map g)))

private def rightCoefficientRoute :=
  smallCoefficientRouteIso boundedFlatPerfectPseudofunctor
    (inputSchemeMap Q g).op (coefficientMap Q Y).op
    (evaluationRawNormalization (inputSchemeMap Q g))
    (tensorCoefficientNormalization (coefficientMap Q Y))

private theorem leftRoute_normalized :
    modelEvaluationInputLeft Q g =
      (isoSquareConjugate (leftCoefficientRoute Q g)
        (evaluationNormalizationIso (op (scheme Q X)))
        (evaluationNormalizationIso (op (scheme Q (laurent.op.obj Y))))).symm := by
  rw [modelEvaluationInputLeft_route, internalTensorModelIso_smallCoefficient,
    evaluationComparisonIso_smallCoefficient]
  apply congrArg Iso.symm
  exact isoSquareRoute_conjugate _ _ _ _ _

private theorem rightRoute_normalized :
    modelEvaluationInputRight Q g =
      (isoSquareConjugate (rightCoefficientRoute Q g)
        (evaluationNormalizationIso (op (scheme Q X)))
        (evaluationNormalizationIso (op (scheme Q (laurent.op.obj Y))))).symm := by
  rw [modelEvaluationInputRight_route, internalTensorModelIso_smallCoefficient,
    evaluationComparisonIso_smallCoefficient]
  apply congrArg Iso.symm
  exact isoSquareRoute_conjugate _ _ _ _ _

/-- Both actual Model evaluation routes recover the original geometric reindex square. -/
theorem modelEvaluationInputSquare_hom :
    (rawEvaluatedInputIso Q g).hom ≫ (modelEvaluationInputRight Q g).hom =
      (modelEvaluationInputLeft Q g).hom ≫
        eqToHom (congrArg (fun F => F ⋙
          (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor)
          (globalReindexInputSquare (coefficientMap Q X) (coefficientMap Q Y)
            (inputSchemeMap Q (laurent.op.map g)) (inputSchemeMap Q g)
            (coefficientMap_input Q g))) := by
  have hs := isoSquareConjugate_rectangle
    (smallCoefficientRouteIso boundedFlatPerfectPseudofunctor
      (coefficientMap Q X).op (inputSchemeMap Q (laurent.op.map g)).op
      (tensorCoefficientNormalization (coefficientMap Q X))
      (evaluationRawNormalization (inputSchemeMap Q (laurent.op.map g))))
    (smallCoefficientRouteIso boundedFlatPerfectPseudofunctor
      (inputSchemeMap Q g).op (coefficientMap Q Y).op
      (evaluationRawNormalization (inputSchemeMap Q g))
      (tensorCoefficientNormalization (coefficientMap Q Y)))
    (smallCoefficientInputSquareIso boundedFlatPerfectPseudofunctor
      (coefficientMap Q X).op (inputSchemeMap Q (laurent.op.map g)).op
      (inputSchemeMap Q g).op (coefficientMap Q Y).op
      (congrArg (fun f => f.op) (coefficientMap_input Q g))
      (tensorCoefficientNormalization (coefficientMap Q X))
      (evaluationRawNormalization (inputSchemeMap Q (laurent.op.map g)))
      (evaluationRawNormalization (inputSchemeMap Q g))
      (tensorCoefficientNormalization (coefficientMap Q Y)))
    (originalReindexInputSquare boundedFlatPerfectPseudofunctor
      (coefficientMap Q X).op (inputSchemeMap Q (laurent.op.map g)).op
      (inputSchemeMap Q g).op (coefficientMap Q Y).op
      (congrArg (fun f => f.op) (coefficientMap_input Q g)))
    (evaluationNormalizationIso (op (scheme Q X)))
    (evaluationNormalizationIso (op (scheme Q (laurent.op.obj Y))))
    (smallCoefficientInputSquare_hom boundedFlatPerfectPseudofunctor
      (coefficientMap Q X).op (inputSchemeMap Q (laurent.op.map g)).op
      (inputSchemeMap Q g).op (coefficientMap Q Y).op
      (congrArg (fun f => f.op) (coefficientMap_input Q g))
      (tensorCoefficientNormalization (coefficientMap Q X))
      (evaluationRawNormalization (inputSchemeMap Q (laurent.op.map g)))
      (evaluationRawNormalization (inputSchemeMap Q g))
      (tensorCoefficientNormalization (coefficientMap Q Y)))
  rw [leftRoute_normalized, rightRoute_normalized]
  unfold rawEvaluatedInputIso
  rw [tensorUnitRawModelInputIso_eq]
  exact hs

private theorem whiskerRight_transport {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (h : F = G) (J : D ⥤ E) :
    whiskerRight (eqToHom h) J = eqToHom (congrArg (fun K => K ⋙ J) h) := by
  subst G
  simp

/-- The displayed original strict parameter square has the same literal source transport. -/
theorem coefficientFunctorSquare_evaluation :
    (isoWhiskerRight (coefficientFunctorSquare (ParameterModels.ambient Q) g)
      (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor).hom =
      eqToHom (congrArg (fun F => F ⋙
        (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor)
        (globalReindexInputSquare (coefficientMap Q X) (coefficientMap Q Y)
          (inputSchemeMap Q (laurent.op.map g)) (inputSchemeMap Q g)
          (coefficientMap_input Q g))) := by
  simp only [coefficientFunctorSquare, isoWhiskerRight_hom, eqToIso.hom,
    whiskerRight_transport]

attribute [local irreducible] rawEvaluatedInputIso
  modelEvaluationInputLeft modelEvaluationInputRight

/-- The full specified movement square identifies genuine raw tensor with the strict input. -/
theorem modelEvaluationInputSquare :
    modelEvaluationInputLeft Q g ≪≫
        isoWhiskerRight (coefficientFunctorSquare (ParameterModels.ambient Q) g)
          (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor =
      rawEvaluatedInputIso Q g ≪≫ modelEvaluationInputRight Q g := by
  apply Iso.ext
  change (modelEvaluationInputLeft Q g).hom ≫ _ =
    (rawEvaluatedInputIso Q g).hom ≫ (modelEvaluationInputRight Q g).hom
  rw [coefficientFunctorSquare_evaluation]
  exact (modelEvaluationInputSquare_hom Q g).symm

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
