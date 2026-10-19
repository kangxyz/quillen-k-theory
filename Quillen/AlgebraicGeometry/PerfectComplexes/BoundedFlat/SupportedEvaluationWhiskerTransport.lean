/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedReindexWhiskerTransport

/-! # Whole equality transport after actual supported evaluation

The original two-edge supported section routes retain their ambient functors under actual
evaluation and inclusion. Their entire strict equality transport is compared before taking
components, preserving the original square in the supported section category.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation

/-- Actual evaluation and inclusion preserve the entire original two-edge section functor. -/
theorem supportedEvaluationRoute_forget {A B C : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    (((supportedPairModelMap g).functor ⋙ (supportedPairModelMap f).functor) ⋙
        supportedEvaluation (X := op A.obj.right) A.obj.hom) ⋙
        tensorCoefficientSupportedForget A.obj.hom =
      (supported (X := op C.obj.right) C.obj.hom).ι ⋙
        (((globalModel.map g.hom.right.op).functor ⋙
          (globalModel.map f.hom.right.op).functor) ⋙ globalEvaluation (op A.obj.right)) := rfl

/-- The entire evaluated two-edge forget comparison is the identity transformation. -/
theorem supportedEvaluationRoute_forget_hom {A B C : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    eqToHom (supportedEvaluationRoute_forget f g) =
      𝟙 ((supported (X := op C.obj.right) C.obj.hom).ι ⋙
        (((globalModel.map g.hom.right.op).functor ⋙
          (globalModel.map f.hom.right.op).functor) ⋙ globalEvaluation (op A.obj.right))) := rfl

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The complete evaluated supported transport retains the original ambient transport. -/
theorem supportedEvaluationEquality_forget_whisker :
    whiskerRight (eqToHom (congrArg (fun F => F ⋙
        supportedEvaluation (X := op C.obj.right) C.obj.hom)
        (supportedReindexInputSquare p q a b h)))
        (tensorCoefficientSupportedForget C.obj.hom) =
      whiskerLeft (supported (X := op B.obj.right) B.obj.hom).ι
        (eqToHom (congrArg (fun F => F ⋙ globalEvaluation (op C.obj.right))
          (globalReindexInputSquare p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h)))) := by
  have he := Functor.eqToHom_whisker_square
    (supported (X := op B.obj.right) B.obj.hom).ι
    (tensorCoefficientSupportedForget C.obj.hom)
    (((supportedPairModelMap p).functor ⋙ (supportedPairModelMap a).functor) ⋙
      supportedEvaluation (X := op C.obj.right) C.obj.hom)
    (((supportedPairModelMap b).functor ⋙ (supportedPairModelMap q).functor) ⋙
      supportedEvaluation (X := op C.obj.right) C.obj.hom)
    (((globalModel.map p.hom.right.op).functor ⋙ (globalModel.map a.hom.right.op).functor) ⋙
      globalEvaluation (op C.obj.right))
    (((globalModel.map b.hom.right.op).functor ⋙ (globalModel.map q.hom.right.op).functor) ⋙
      globalEvaluation (op C.obj.right))
    (congrArg (fun F => F ⋙ supportedEvaluation (X := op C.obj.right) C.obj.hom)
      (supportedReindexInputSquare p q a b h))
    (congrArg (fun F => F ⋙ globalEvaluation (op C.obj.right))
      (globalReindexInputSquare p.hom.right q.hom.right a.hom.right b.hom.right
        (congrArg (fun f : C ⟶ B => f.hom.right) h)))
    (supportedEvaluationRoute_forget a p) (supportedEvaluationRoute_forget q b)
  rw [supportedEvaluationRoute_forget_hom q b, supportedEvaluationRoute_forget_hom a p] at he
  exact (Category.comp_id _).symm.trans (he.trans (Category.id_comp _))

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
