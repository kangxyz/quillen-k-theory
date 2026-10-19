/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputRoutes

/-! # Actual evaluation-forgetting before choosing an ambient isomorphism

The original supported evaluation and full-subcategory inclusion agree as whiskering
operations on an arbitrary ambient isomorphism. This separates the actual evaluation
functor identity from any later geometric composition records.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation
  evaluationPullbackIso supportedPairReindexEvaluationIso
universe v w

/-- Actual evaluation and support inclusion agree before any ambient isomorphism is chosen. -/
theorem supportedEvaluation_forget_whiskerIso
    {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]
    {T : Type v} [Category.{w} T]
    {P Q : (boundedFlatPerfect X.unop).FullSubcategory ⥤ T} (e : P ≅ Q) :
    isoWhiskerLeft (supportedEvaluation j)
        (isoWhiskerLeft (tensorCoefficientSupportedForget j) e) =
      isoWhiskerLeft (supported j).ι (isoWhiskerLeft (globalEvaluation X) e) := rfl

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
