/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationWhiskerTransport

/-! # Genuine equality transports through supported evaluation

The independently formed geometric square and the original strict section transport retain
their ambient components under the actual full-subcategory inclusion. These are categorical
morphism identities before normalization or realization.
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
/-- Original supported evaluation preserves the actual section inclusion on every map. -/
theorem supportedEvaluation_forget_map {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j]
    {L M : (supported j).FullSubcategory} (f : L ⟶ M) :
    (tensorCoefficientSupportedForget j).map ((supportedEvaluation j).map f) =
      (globalEvaluation X).map ((supported j).ι.map f) := rfl

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
  (K : (supported (X := op B.obj.right) B.obj.hom).FullSubcategory)

/-- The original supported reindex transport retains its strict ambient transport component. -/
theorem supportedReindexInput_forget_hom_app :
    (tensorCoefficientSupportedForget C.obj.hom).map
        ((eqToHom (congrArg (fun F => F ⋙
          supportedEvaluation (X := op C.obj.right) C.obj.hom)
          (supportedReindexInputSquare p q a b h))).app K) =
      (eqToHom (congrArg (fun F => F ⋙ globalEvaluation (op C.obj.right))
        (globalReindexInputSquare p.hom.right q.hom.right a.hom.right b.hom.right
          (congrArg (fun f : C ⟶ B => f.hom.right) h)))).app K.obj := by
  exact NatTrans.congr_app (supportedEvaluationEquality_forget_whisker p q a b h) K

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
