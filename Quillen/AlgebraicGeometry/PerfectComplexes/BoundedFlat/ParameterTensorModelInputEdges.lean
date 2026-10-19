/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorModelInputRoutes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitNormalizedInputSquare
public import Quillen.Waldhausen.SmallModel.CoefficientInputSquare
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationNormalization

/-! # Exact normalized evaluation edges of the genuine parameter tensor square

Each displayed Model comparison is the original small coefficient comparison conjugated by
its specified evaluation normalizations. These are equalities of the actual isomorphisms,
so their movement paths remain available in the first-S prism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.CategoryTheory.GrothendieckSections
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

private theorem inverseRoute {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {a : A ⥤ B} {b : B ⥤ C} {N : D ⥤ E} {M : E ⥤ F}
    {E₀ : A ⥤ D} {E₁ : B ⥤ E} {E₂ : C ⥤ F}
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M) :
    isoWhiskerRight s.symm M ≪≫ Functor.associator a E₁ M ≪≫
        isoWhiskerLeft a t.symm ≪≫ (Functor.associator a b E₂).symm =
      (isoSquareRoute s t).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [isoSquareRoute]

attribute [local irreducible] evaluationNormalizationIso
  tensorUnitPullbackNormalization boundedFlatPerfectTensorUnitPullbackIso
  originalCoefficientIso

private theorem tensorWhisker {C : Type*} [Category* C]
    {D E : Type v} [Category.{w} D] [Category.{w} E]
    (A : C ⥤ D) (B : C ⥤ E) (P T N : D ⥤ E)
    (v : T ≅ P) (c : A ⋙ P ≅ B) (n : T ≅ N) :
    smallModelWhiskerIso A B T N ((isoWhiskerLeft A v) ≪≫ c).symm n =
      isoWhiskerRight (c.symm ≪≫ isoWhiskerLeft A (v.symm ≪≫ n))
        AsSmall.up.{w, v, 0} := by
  simp only [smallModelWhiskerIso, Iso.trans_symm, isoWhiskerLeft_symm,
    isoWhiskerLeft_trans, Iso.trans_assoc]

private theorem tensorMiddleIso_coefficient (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    tensorMiddleIso Q X =
      isoWhiskerRight
        (normalizedCoefficientIso boundedFlatPerfectPseudofunctor (coefficientMap Q X).op
          (tensorCoefficientNormalization (coefficientMap Q X))) AsSmall.up.{u, u + 1, 0} := by
  have h := tensorWhisker
    (globalEvaluation (op (scheme Q X)))
    ((globalModel.map (coefficientMap Q X).op).functor ⋙
      globalEvaluation (op (scheme Q (laurent.op.obj X))))
    (boundedFlatPerfectPullback (coefficientMap Q X))
    (boundedFlatPerfectTensorUnitPullback (coefficientMap Q X)) _
    (boundedFlatPerfectTensorUnitPullbackIso (coefficientMap Q X))
    (evaluationPullbackIso (coefficientMap Q X))
    (tensorUnitPullbackNormalization (coefficientMap Q X))
  simpa only [tensorMiddleIso, tensorEvaluationIso, normalizedCoefficientIso,
    tensorCoefficientNormalization, evaluationPullbackIso_original, Iso.symm_symm_eq,
    globalEvaluation, evaluationSmall] using h

/-- The original tensor/evaluation Model edge retains its exact small coefficient comparison. -/
theorem internalTensorModelIso_smallCoefficient (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    internalTensorModelIso Q X =
      isoSquareConjugate
        (smallCoefficientIso boundedFlatPerfectPseudofunctor (coefficientMap Q X).op
          (tensorCoefficientNormalization (coefficientMap Q X)))
        (evaluationNormalizationIso (op (scheme Q X)))
        (evaluationNormalizationIso (op (scheme Q (laurent.op.obj X)))) := by
  simp only [internalTensorModelIso, isoSquareConjugate, smallCoefficientIso,
    tensorMiddleIso_coefficient, Iso.trans_assoc]
  rfl

/-- The displayed tensor-first route is the inverse of the actual two-edge pasting. -/
theorem modelEvaluationInputLeft_route (Q : Scheme.{u})
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    modelEvaluationInputLeft Q g =
      (isoSquareRoute (internalTensorModelIso Q X)
        (evaluationComparisonIso (inputSchemeMap Q (laurent.op.map g)))).symm := by
  exact inverseRoute (internalTensorModelIso Q X)
    (evaluationComparisonIso (inputSchemeMap Q (laurent.op.map g)))

/-- The displayed tensor-second route is the inverse of its actual two-edge pasting. -/
theorem modelEvaluationInputRight_route (Q : Scheme.{u})
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    modelEvaluationInputRight Q g =
      (isoSquareRoute (evaluationComparisonIso (inputSchemeMap Q g))
        (internalTensorModelIso Q Y)).symm := by
  exact inverseRoute (evaluationComparisonIso (inputSchemeMap Q g))
    (internalTensorModelIso Q Y)

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
