/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackInputForgetIso
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationForgetWhiskerIso

/-! # The whole original supported geometric square under evaluation

Actual supported evaluation preserves the entire independently formed geometric input square
under the original support inclusion. The comparison retains both original pullback
composition isomorphisms and their intervening equality transport before components.
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
private theorem leftRight_eq {E F G H : Type*}
    [Category* E] [Category* F] [Category* G] [Category* H]
    {P Q : E ⥤ F} (e : P ≅ Q) (J : F ⥤ G)
    (e' : P ⋙ J ≅ Q ⋙ J) (h : isoWhiskerRight e J = e') (L : H ⥤ E) :
    isoWhiskerRight (isoWhiskerLeft L e) J = isoWhiskerLeft L e' := by
  subst e'
  rfl

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- Actual supported evaluation retains the whole geometric input comparison after inclusion. -/
theorem supportedEvaluationRawInput_forget_iso :
    isoWhiskerRight
        (isoWhiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom)
          (supportedPullbackInputSquareIso p q a b h))
        (tensorCoefficientSupportedForget C.obj.hom) =
      isoWhiskerLeft (supported (X := op B.obj.right) B.obj.hom).ι
        (isoWhiskerLeft (globalEvaluation (op B.obj.right))
          (pullbackInputSquareIso p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h))) := by
  exact (leftRight_eq (supportedPullbackInputSquareIso p q a b h)
    (tensorCoefficientSupportedForget C.obj.hom) _
    (supportedPullbackInputSquareIso_forget p q a b h)
    (supportedEvaluation (X := op B.obj.right) B.obj.hom)).trans
      (supportedEvaluation_forget_whiskerIso (X := op B.obj.right) B.obj.hom
        (T := (boundedFlatPerfect C.obj.right).FullSubcategory)
        (P := boundedFlatPerfectPullback p.hom.right ⋙ boundedFlatPerfectPullback a.hom.right)
        (Q := boundedFlatPerfectPullback b.hom.right ⋙ boundedFlatPerfectPullback q.hom.right)
        (pullbackInputSquareIso p.hom.right q.hom.right a.hom.right b.hom.right
          (congrArg (fun f : C ⟶ B => f.hom.right) h)))

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
