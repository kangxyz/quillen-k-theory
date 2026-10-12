/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.FiberedCategory.GrothendieckUnderRestriction
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckMapFiber

/-!
# Evaluation of the original pseudonatural section restriction

Evaluation of the actual restricted section is the original evaluation followed by the
specified pseudonatural component. The proof retains the original vertical inclusion,
rebracketing and unit comparison, and uses no inverse evaluation choice.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckFiber
open Quillen.CategoryTheory.GrothendieckUnderSections
open Quillen.CategoryTheory.GrothendieckSections
universe u v w w' u' v'
namespace Quillen.CategoryTheory.GrothendieckUnderRestriction
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
    (K : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (R : C)
    (G : Pseudofunctor (LocallyDiscrete (Under R)) Cat.{v', u'})
    (α : Pseudofunctor.StrongTrans ((Under.forget R ⋙ K).toPseudofunctor.comp F) G)

/-- Original restricted objects evaluate to the specified component on the original fiber. -/
theorem sectionFunctor_evaluation_obj (a : Under R)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget
      (K.toPseudofunctor.comp F)) a.right) :
    (originalEvaluation G a).obj ((sectionFunctor K F R G α a).obj s) =
      (α.app ⟨a⟩).toFunctor.obj
        ((originalEvaluation (K.toPseudofunctor.comp F) a.right).obj s) := rfl

/-- The original vertical maps evaluate by the same original component functor. -/
theorem sectionFunctor_evaluation_map (a : Under R)
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget
      (K.toPseudofunctor.comp F)) a.right} (f : s ⟶ t) :
    (originalEvaluation G a).map ((sectionFunctor K F R G α a).map f) =
      (α.app ⟨a⟩).toFunctor.map
        ((originalEvaluation (K.toPseudofunctor.comp F) a.right).map f) := by
  have hr := GrothendieckUnderComposition.rebracket_inclusion_map K F R a
    ((originalEvaluation (K.toPseudofunctor.comp F) a.right).map f)
  have ht := (congrArg (Pseudofunctor.Grothendieck.map α).map hr).trans
    (map_inclusion α a ((originalEvaluation (K.toPseudofunctor.comp F) a.right).map f))
  change (fromFiber G a).map
    ((underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget G) a).map
      ((sectionFunctor K F R G α a).map f)) = _
  apply (toFiber G a).map_injective
  rw [toFiber_map_fromFiber_map]
  apply Subtype.ext
  change (𝟙 _ ≫ (totalFunctor K F R G α).map
    ((inclusion (pseudofunctor (K.toPseudofunctor.comp F) R) a).map
      ((originalEvaluation (K.toPseudofunctor.comp F) a.right).map f)) ≫ 𝟙 _) = _
  simpa only [totalFunctor, Functor.comp_obj, Functor.comp_map, toFiber,
    Functor.Fiber.inducedFunctor, Category.id_comp, Category.comp_id] using ht

/-- Evaluation is literally the original evaluation followed by the supplied component. -/
theorem sectionFunctor_comp_evaluation (a : Under R) :
    sectionFunctor K F R G α a ⋙ originalEvaluation G a =
      originalEvaluation (K.toPseudofunctor.comp F) a.right ⋙ (α.app ⟨a⟩).toFunctor := by
  fapply Functor.ext
  · intro s
    exact sectionFunctor_evaluation_obj K F R G α a s
  · intro s t f
    simpa only [Functor.comp_obj, Functor.comp_map, eqToHom_refl,
      Category.id_comp, Category.comp_id] using
      sectionFunctor_evaluation_map K F R G α a f

end Quillen.CategoryTheory.GrothendieckUnderRestriction
