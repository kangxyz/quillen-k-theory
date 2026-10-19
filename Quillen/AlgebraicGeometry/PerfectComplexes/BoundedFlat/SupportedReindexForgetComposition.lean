/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputRoutes

/-! # Literal forgetting of two original supported reindex maps

The original two-edge supported section route forgets to the two ambient section maps as a
whole functor. Its equality comparison has identity components before any square transport.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation
variable {A B C : Scheme.OpenPairs.{u}} (f : A ⟶ B) (g : B ⟶ C)

/-- Forgetting the actual two-edge supported route preserves the original ambient functor. -/
theorem supportedReindexRoute_forget :
    ((supportedPairModelMap g).functor ⋙ (supportedPairModelMap f).functor) ⋙
        (supported (X := op A.obj.right) A.obj.hom).ι =
      (supported (X := op C.obj.right) C.obj.hom).ι ⋙
        ((globalModel.map g.hom.right.op).functor ⋙
          (globalModel.map f.hom.right.op).functor) := rfl

/-- The literal two-edge forget comparison has identity components. -/
theorem supportedReindexRoute_forget_hom_app
    (K : (supported (X := op C.obj.right) C.obj.hom).FullSubcategory) :
    (eqToHom (supportedReindexRoute_forget f g)).app K =
      𝟙 ((globalModel.map f.hom.right.op).functor.obj
        ((globalModel.map g.hom.right.op).functor.obj K.obj)) := rfl

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
