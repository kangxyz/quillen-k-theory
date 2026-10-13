/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.FiberedCategory.CocartesianSectionComposition
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckCocartesianMap
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Actual restriction of Grothendieck sections to a fixed coslice base

An existing section over all arrows from the target of a fixed coefficient object is restricted
along the original coslice forgetful functor. Its fiber objects and arrows are the original
ones, with only their proved base equalities transported. In particular no inverse evaluation
functor or new cocartesian lift is chosen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckUnderSections
variable {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C)

/-- The original pseudofunctor restricted along the actual coslice projection. -/
def pseudofunctor : Pseudofunctor (LocallyDiscrete (Under R)) Cat.{v', u'} :=
  (Under.forget R).toPseudofunctor.comp F

/-- The original unit constraint is retained by restriction along the coslice projection. -/
theorem mapId_hom (a : Under R) (x : F.obj ⟨a.right⟩) :
    ((pseudofunctor F R).mapId ⟨a⟩).hom.toNatTrans.app x =
      (F.mapId ⟨a.right⟩).hom.toNatTrans.app x := by
  simp [pseudofunctor, Pseudofunctor.comp, Functor.toPseudofunctor]

/-- Restriction retains the original composition constraint at every fiber object. -/
theorem mapComp_hom {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c)
    (x : F.obj ⟨a.right⟩) :
    ((pseudofunctor F R).mapComp f.toLoc g.toLoc).hom.toNatTrans.app x =
      (F.mapComp f.right.toLoc g.right.toLoc).hom.toNatTrans.app x := by
  simp [pseudofunctor, Pseudofunctor.comp, Functor.toPseudofunctor]
  rfl

/-- Actual coefficient restriction retains each original fiber object and transition. -/
def sectionFunctor (a : Under R)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) a.right) :
    Under a ⥤ Pseudofunctor.Grothendieck (pseudofunctor F R) where
  obj i := ⟨i.right, (originalEvaluationAt F a.right
    ((Under.post (Under.forget R)).obj i)).obj s⟩
  map f := ⟨f.right, originalArrowTransition F a.right s
    ((Under.post (Under.forget R)).map f)⟩
  map_id i := by
    refine Pseudofunctor.Grothendieck.Hom.ext (F := pseudofunctor F R) _ _ ?_ ?_
    · rfl
    simp only [eqToHom_refl, Category.id_comp,
      Pseudofunctor.Grothendieck.categoryStruct_id_fiber, mapId_hom]
    exact originalArrowTransition_id F a.right s ((Under.post (Under.forget R)).obj i)
  map_comp f g := by
    refine Pseudofunctor.Grothendieck.Hom.ext (F := pseudofunctor F R) _ _ ?_ ?_
    · rfl
    simp only [eqToHom_refl, Category.id_comp,
      Pseudofunctor.Grothendieck.categoryStruct_comp_fiber, mapComp_hom]
    exact originalArrowTransition_comp F a.right s
      ((Under.post (Under.forget R)).map f) ((Under.post (Under.forget R)).map g)

/-- The constructed section is literally over the original coslice projection. -/
theorem sectionFunctor_comp (a : Under R)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) a.right) :
    sectionFunctor F R a s ⋙ Pseudofunctor.Grothendieck.forget (pseudofunctor F R) =
      Under.forget a := rfl

/-- The original arrow transition is invertible, by the source section's cocartesianness. -/
theorem isIso_originalArrowTransition (A : C)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) A)
    {i k : Under A} (f : i ⟶ k) : IsIso (originalArrowTransition F A s f) := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f.right
      (s.obj.val.map f) := s.property f
  exact GrothendieckFiber.isIso_liftedMap F f.right
    (x := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget A) i).obj s)
    (y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget A) k).obj s) (s.obj.val.map f)

/-- Every retained original transition is strongly cocartesian in the restricted total category. -/
def restrictedSection (a : Under R)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) a.right) :
    underCocartesian (Pseudofunctor.Grothendieck.forget (pseudofunctor F R)) a :=
  ⟨⟨sectionFunctor F R a s, sectionFunctor_comp F R a s⟩, fun _ _ f => by
    have : IsIso ((sectionFunctor F R a s).map f).fiber :=
      isIso_originalArrowTransition F a.right s ((Under.post (Under.forget R)).map f)
    exact GrothendieckCocartesian.of_isIso_fiber ((sectionFunctor F R a s).map f)⟩


end Quillen.CategoryTheory.GrothendieckUnderSections
