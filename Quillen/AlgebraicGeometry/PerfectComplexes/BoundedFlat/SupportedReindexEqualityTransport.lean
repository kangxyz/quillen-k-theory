/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedReindexWhiskerTransport

/-! # The original supported section equality under inclusion

The actual supported reindex square retains its ambient section component before evaluation.
This separates the section inclusion from the independently lifted supported evaluation.
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
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
  (K : (supported (X := op B.obj.right) B.obj.hom).FullSubcategory)

/-- The strict supported square preserves its entire ambient section transport component. -/
theorem supportedReindexEquality_forget_hom_app :
    (supported (X := op C.obj.right) C.obj.hom).ι.map
        ((eqToHom (supportedReindexInputSquare p q a b h)).app K) =
      (eqToHom (globalReindexInputSquare p.hom.right q.hom.right a.hom.right b.hom.right
        (congrArg (fun f : C ⟶ B => f.hom.right) h))).app K.obj :=
  NatTrans.congr_app (supportedReindexEquality_forget_whisker p q a b h) K

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
