/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationModel
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationModel
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientInputNaturality
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-! # The original support-forgetting evaluation edge with both zero comparisons

Forgetting support uses the original full-subcategory inclusion and its original geometric
zero rebase. The evaluation comparison retains that rebase, the actual common-universe
transport, and both independently chosen evaluation-zero normalization isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation
/-- The original raw evaluation-forgetting square keeps each underlying bounded-flat complex. -/
def evaluationForgetIso {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] :
    (supportedForget j).functor ⋙ globalEvaluation X ≅
      supportedEvaluation j ⋙ tensorCoefficientSupportedForget j :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The actual support inclusion with precisely its existing selected-zero normalization. -/
def forgetRawNormalization :=
  Quillen.rebaseFunctorIso (tensorCoefficientSupportedForget j)
    (boundedFlatPerfectSupportedWaldhausen j).zero
    (boundedFlatPerfectWaldhausen X.unop).zero
    (((tensorCoefficientSupportedForget_exact j).zero
      (boundedFlatPerfectSupportedWaldhausen j).isZero).iso
      (boundedFlatPerfectWaldhausen X.unop).isZero)

/-- Original evaluated support-forgetting before the two evaluation-zero normalizations. -/
def evaluationForgetSmallComparisonIso :
    (supportedForget j).functor ⋙ GlobalSectionChangeIndex.evaluationSmall X ≅
      evaluationSmall j ⋙ (tensorCoefficientSupportedForgetModel j).functor :=
  (Functor.associator _ _ _).symm ≪≫
    smallModelWhiskerIso (supportedEvaluation j)
      ((supportedForget j).functor ⋙ globalEvaluation X)
      (tensorCoefficientSupportedForget j) _
      (evaluationForgetIso j) (forgetRawNormalization j)

/-- The genuine Model-level forgetting edge retains both actual evaluation comparisons. -/
def evaluationForgetModelComparisonIso :
    (supportedForget j ≫ GlobalSectionChangeIndex.evaluationModel X).functor ≅
      (evaluationModel j ≫ tensorCoefficientSupportedForgetModel j).functor :=
  isoSquareConjugate (evaluationForgetSmallComparisonIso j)
    (evaluationNormalizationIso j) (GlobalSectionChangeIndex.evaluationNormalizationIso X)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
