/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedInputRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportMaps

/-! # Genuine tensor rectangles for auxiliary support enlargement and restriction

Every original fixed-factor open-pair square acts on the full supported tensor evaluation
rectangle. The auxiliary enlargement and restriction are its actual geometric specializations,
so all three genuine supported objects are retained, together with their selected zeros.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass.GeometricSeedCospan
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open ParameterTensorSupportedRow SupportedTensorEvaluation
attribute [local irreducible] globalModel globalEvaluation GlobalSupportedParameter.pairMap
variable {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) (X : Scheme.{u}ᵒᵖ)

/-- The actual fixed-factor pair map commutes with the original Laurent coefficient. -/
theorem tensorCoefficientPair_square :
    (pairTransformation g).app (laurent.op.obj X).unop ≫ coefficientPair B.obj.hom X =
      coefficientPair A.obj.hom X ≫ (pairTransformation g).app X.unop :=
  ((pairTransformation g).naturality (coefficient.app X).unop).symm

/-- The original full supported tensor rectangle for any fixed-factor open-pair morphism. -/
theorem tensorInputRectangle :
    rawEvaluatedInputIso (coefficientPair B.obj.hom X) (coefficientPair A.obj.hom X)
        ((pairTransformation g).app (laurent.op.obj X).unop)
        ((pairTransformation g).app X.unop) (tensorCoefficientPair_square g X) ≪≫
        modelEvaluationInputRight (coefficientPair A.obj.hom X)
          ((pairTransformation g).app X.unop) =
      modelEvaluationInputLeft (coefficientPair B.obj.hom X)
          ((pairTransformation g).app (laurent.op.obj X).unop) ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (SupportedTensorEvaluation.evaluationModel
            (X := op (pair A.obj.hom (laurent.op.obj X)).obj.right)
            (pair A.obj.hom (laurent.op.obj X)).obj.hom).functor)
          (supportedReindexInputSquare
            (coefficientPair B.obj.hom X) (coefficientPair A.obj.hom X)
            ((pairTransformation g).app (laurent.op.obj X).unop)
            ((pairTransformation g).app X.unop) (tensorCoefficientPair_square g X))) :=
  modelEvaluationInputRectangle _ _ _ _ _

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The full genuine tensor rectangle for the original union-to-auxiliary support enlargement. -/
theorem tensorEnlargementInputRectangle (X : Scheme.{u}ᵒᵖ) :
    rawEvaluatedInputIso (coefficientPair (unionOpen f T).ι X) (coefficientPair T.ι X)
        ((pairTransformation (enlargementPair f T)).app (laurent.op.obj X).unop)
        ((pairTransformation (enlargementPair f T)).app X.unop)
          (tensorCoefficientPair_square (enlargementPair f T) X) ≪≫
        modelEvaluationInputRight (coefficientPair T.ι X)
          ((pairTransformation (enlargementPair f T)).app X.unop) =
      modelEvaluationInputLeft (coefficientPair (unionOpen f T).ι X)
          ((pairTransformation (enlargementPair f T)).app (laurent.op.obj X).unop) ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (SupportedTensorEvaluation.evaluationModel
            (X := op (pair T.ι (laurent.op.obj X)).obj.right)
            (pair T.ι (laurent.op.obj X)).obj.hom).functor)
          (supportedReindexInputSquare
            (coefficientPair (unionOpen f T).ι X) (coefficientPair T.ι X)
            ((pairTransformation (enlargementPair f T)).app (laurent.op.obj X).unop)
            ((pairTransformation (enlargementPair f T)).app X.unop)
          (tensorCoefficientPair_square (enlargementPair f T) X))) :=
  tensorInputRectangle (enlargementPair f T) X

omit [IsOpenImmersion f] in
/-- The full genuine tensor rectangle for the original auxiliary-to-inverse-open restriction. -/
theorem tensorRestrictionInputRectangle (X : Scheme.{u}ᵒᵖ) :
    rawEvaluatedInputIso (coefficientPair T.ι X) (coefficientPair (inverseOpen f T).ι X)
        ((pairTransformation (supportRestrictionPair f T)).app (laurent.op.obj X).unop)
        ((pairTransformation (supportRestrictionPair f T)).app X.unop)
          (tensorCoefficientPair_square (supportRestrictionPair f T) X) ≪≫
        modelEvaluationInputRight (coefficientPair (inverseOpen f T).ι X)
          ((pairTransformation (supportRestrictionPair f T)).app X.unop) =
      modelEvaluationInputLeft (coefficientPair T.ι X)
          ((pairTransformation (supportRestrictionPair f T)).app (laurent.op.obj X).unop) ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (SupportedTensorEvaluation.evaluationModel
            (X := op (pair (inverseOpen f T).ι (laurent.op.obj X)).obj.right)
            (pair (inverseOpen f T).ι (laurent.op.obj X)).obj.hom).functor)
          (supportedReindexInputSquare
            (coefficientPair T.ι X) (coefficientPair (inverseOpen f T).ι X)
            ((pairTransformation (supportRestrictionPair f T)).app (laurent.op.obj X).unop)
            ((pairTransformation (supportRestrictionPair f T)).app X.unop)
          (tensorCoefficientPair_square (supportRestrictionPair f T) X))) :=
  tensorInputRectangle (supportRestrictionPair f T) X

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
