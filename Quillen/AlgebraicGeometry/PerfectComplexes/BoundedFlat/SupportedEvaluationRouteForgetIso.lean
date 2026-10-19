/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputRoutes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationWhiskerTransport

/-! # Entire original supported evaluation routes after inclusion

The original supported evaluation routes and their original strict reindex transport keep
their whole ambient isomorphisms under the actual full-subcategory inclusion. The two-edge
routes are retained before assembling the full supported input rectangle.
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
  supportedEvaluationRouteIso evaluationPullbackRouteIso
/-- Both complete original supported evaluation transitions retain their ambient Iso. -/
theorem supportedEvaluationRoute_forget_iso {A B C : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    isoWhiskerRight (supportedEvaluationRouteIso f g)
        (tensorCoefficientSupportedForget A.obj.hom) =
      isoWhiskerLeft (supported (X := op C.obj.right) C.obj.hom).ι
        (evaluationPullbackRouteIso f.hom.right g.hom.right) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact supportedEvaluationRoute_forget_hom_app f g K

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The entire actual evaluated supported equality Iso retains its ambient transport. -/
theorem supportedEvaluationEquality_forget_iso :
    isoWhiskerRight (eqToIso (congrArg (fun F => F ⋙
        supportedEvaluation (X := op C.obj.right) C.obj.hom)
        (supportedReindexInputSquare p q a b h)))
        (tensorCoefficientSupportedForget C.obj.hom) =
      isoWhiskerLeft (supported (X := op B.obj.right) B.obj.hom).ι
        (eqToIso (congrArg (fun F => F ⋙ globalEvaluation (op C.obj.right))
          (globalReindexInputSquare p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h)))) :=
  Iso.ext (supportedEvaluationEquality_forget_whisker p q a b h)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
