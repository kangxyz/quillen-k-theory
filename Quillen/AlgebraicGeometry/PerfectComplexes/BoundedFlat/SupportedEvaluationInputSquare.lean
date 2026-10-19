/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationRawInputForgetIso
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationRouteForgetIso
public import Mathlib.CategoryTheory.Whiskering

/-! # Original evaluation on arbitrary supported pair input squares

The actual supported geometric transitions form a complete two-route square. Its proof
uses the faithful inclusion on entire natural isomorphisms of the original supported
category, with all geometric composition and section reindex transports retained.
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
  supportedPullbackInputSquareIso pullbackInputSquareIso
  supportedEvaluationRouteIso evaluationPullbackRouteIso
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

private theorem rightIso_injective {E F G : Type*}
    [Category* E] [Category* F] [Category* G]
    (J : F ⥤ G) [J.Faithful] {P Q : E ⥤ F} {e e' : P ≅ Q}
    (h : isoWhiskerRight e J = isoWhiskerRight e' J) : e = e' :=
  ((whiskeringRight E F G).obj J).mapIso_injective h

private theorem leftIso_rectangle {E F G : Type*}
    [Category* E] [Category* F] [Category* G] (I : E ⥤ F)
    {P Q R S : F ⥤ G} (r : P ≅ Q) (s : Q ≅ S) (l : P ≅ R) (t : R ≅ S)
    (h : r ≪≫ s = l ≪≫ t) :
    isoWhiskerLeft I r ≪≫ isoWhiskerLeft I s =
      isoWhiskerLeft I l ≪≫ isoWhiskerLeft I t := by
  rw [← isoWhiskerLeft_trans, ← isoWhiskerLeft_trans]
  exact congrArg (isoWhiskerLeft I) h

private theorem ambientInputIso {E F G H : Scheme.{u}}
    (p : E ⟶ F) (q : G ⟶ H) (a : G ⟶ E) (b : H ⟶ F) (h : a ≫ p = q ≫ b) :
    isoWhiskerLeft (globalEvaluation (op F)) (pullbackInputSquareIso p q a b h) ≪≫
        evaluationPullbackRouteIso q b =
      evaluationPullbackRouteIso a p ≪≫
        eqToIso (congrArg (fun F => F ⋙ globalEvaluation (op G))
          (globalReindexInputSquare p q a b h)) :=
  Iso.ext (evaluationPullbackInputSquare_hom p q a b h)

/-- The complete original geometric input rectangle holds inside the actual supported category. -/
theorem supportedEvaluationInputSquare_iso :
    isoWhiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom)
        (supportedPullbackInputSquareIso p q a b h) ≪≫
        supportedEvaluationRouteIso q b =
      supportedEvaluationRouteIso a p ≪≫
        eqToIso (congrArg (fun F => F ⋙
          supportedEvaluation (X := op C.obj.right) C.obj.hom)
          (supportedReindexInputSquare p q a b h)) := by
  let : (tensorCoefficientSupportedForget C.obj.hom).Faithful := by
    unfold tensorCoefficientSupportedForget
    infer_instance
  apply rightIso_injective (tensorCoefficientSupportedForget C.obj.hom)
  rw [isoWhiskerRight_trans, isoWhiskerRight_trans,
    supportedEvaluationRawInput_forget_iso p q a b h,
    supportedEvaluationRoute_forget_iso q b, supportedEvaluationRoute_forget_iso a p,
    supportedEvaluationEquality_forget_iso p q a b h]
  exact leftIso_rectangle (supported (X := op B.obj.right) B.obj.hom).ι _ _ _ _
    (ambientInputIso p.hom.right q.hom.right a.hom.right b.hom.right
      (congrArg (fun f : C ⟶ B => f.hom.right) h))

/-- Actual supported evaluation preserves the complete original geometric input square. -/
theorem supportedEvaluationInputSquare_hom :
    whiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom)
        (supportedPullbackInputSquareIso p q a b h).hom ≫
        (supportedEvaluationRouteIso q b).hom =
      (supportedEvaluationRouteIso a p).hom ≫
        eqToHom (congrArg (fun F => F ⋙
          supportedEvaluation (X := op C.obj.right) C.obj.hom)
          (supportedReindexInputSquare p q a b h)) :=
  congrArg Iso.hom (supportedEvaluationInputSquare_iso p q a b h)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
