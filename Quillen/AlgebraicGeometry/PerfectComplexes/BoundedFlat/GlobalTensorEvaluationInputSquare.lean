/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawInputSquare
public import
  Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationTensorSquare

/-! # Genuine tensor evaluation on the original geometric input square

Both routes retain the actual tensor unitors. Their complete square is the original raw
pullback square evaluated on sections, with the original strict section reindex equality.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The tensor-first route uses its genuine unitor before the original evaluation route. -/
def tensorEvaluationInputLeft :
    globalEvaluation (Opposite.op B) ⋙
        (boundedFlatPerfectTensorUnitPullback p ⋙ boundedFlatPerfectPullback a) ≅
      ((globalModel.map p.op).functor ⋙ (globalModel.map a.op).functor) ⋙
        globalEvaluation (Opposite.op C) :=
  isoWhiskerLeft _ (isoWhiskerRight (boundedFlatPerfectTensorUnitPullbackIso p)
    (boundedFlatPerfectPullback a)) ≪≫ evaluationPullbackRouteIso a p

/-- The tensor-second route retains the second genuine unitor and original evaluation route. -/
def tensorEvaluationInputRight :
    globalEvaluation (Opposite.op B) ⋙
        (boundedFlatPerfectPullback b ⋙ boundedFlatPerfectTensorUnitPullback q) ≅
      ((globalModel.map b.op).functor ⋙ (globalModel.map q.op).functor) ⋙
        globalEvaluation (Opposite.op C) :=
  isoWhiskerLeft _ (isoWhiskerLeft (boundedFlatPerfectPullback b)
    (boundedFlatPerfectTensorUnitPullbackIso q)) ≪≫ evaluationPullbackRouteIso q b

/-- Evaluation preserves the independently constructed genuine tensor input square. -/
theorem tensorEvaluationInputSquare_hom :
    whiskerLeft (globalEvaluation (Opposite.op B))
        (tensorUnitRawInputIso p q a b h).hom ≫
        (tensorEvaluationInputRight q b).hom =
      (tensorEvaluationInputLeft p a).hom ≫
        eqToHom (congrArg (fun F => F ⋙ globalEvaluation (Opposite.op C))
          (globalReindexInputSquare p q a b h)) := by
  exact Quillen.CategoryTheory.GrothendieckSections.originalCoefficientTensorInputSquare_hom
    boundedFlatPerfectPseudofunctor p.op a.op b.op q.op
    (congrArg (fun f : C ⟶ B => f.op) h)
    (boundedFlatPerfectTensorUnitPullback p) (boundedFlatPerfectTensorUnitPullback q)
    (boundedFlatPerfectTensorUnitPullbackIso p) (boundedFlatPerfectTensorUnitPullbackIso q)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
