/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.FiberedCategory.GrothendieckUnderSections
/-!
# Original Grothendieck fibers under coslice composition

Restricting a composed pseudofunctor along the original coslice projection has the same
original total objects and fiber arrows as composing the two original base functors first.
The rebracketing retains the original pseudofunctor constraints; only the identity comparison
of the actual coslice projection is cancelled. It chooses no replacement fiber or lift.
-/
@[expose] public section
open CategoryTheory CategoryTheory.Bicategory
open Quillen.CategoryTheory.GrothendieckUnderSections
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w w' u' v'
namespace Quillen.CategoryTheory.GrothendieckUnderComposition
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
    (K : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (R : C)

/-- The canonical rebracketing is the identity on each original base and fiber component. -/
def rebracket :
    Pseudofunctor.Grothendieck (pseudofunctor (K.toPseudofunctor.comp F) R) ⥤
      Pseudofunctor.Grothendieck ((Under.forget R ⋙ K).toPseudofunctor.comp F) where
  obj x := ⟨x.base, x.fiber⟩
  map f := ⟨f.base, f.fiber⟩
  map_id x := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ ?_ ?_
    · rfl
    simp [pseudofunctor, Pseudofunctor.comp, Functor.toPseudofunctor]
  map_comp f g := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ ?_ ?_
    · rfl
    simp [pseudofunctor, Pseudofunctor.comp, Functor.toPseudofunctor]
    rfl

/-- Original rebracketing does not change the coefficient projection. -/
theorem rebracket_comp :
    rebracket K F R ⋙
        Pseudofunctor.Grothendieck.forget ((Under.forget R ⋙ K).toPseudofunctor.comp F) =
      Pseudofunctor.Grothendieck.forget (pseudofunctor (K.toPseudofunctor.comp F) R) := rfl

/-- The original identity-fiber inclusion retains its actual unit comparison. -/
theorem rebracket_inclusion_map (a : Under R) {x y : F.obj ⟨K.obj a.right⟩} (f : x ⟶ y) :
    (rebracket K F R).map
        ((Quillen.CategoryTheory.GrothendieckFiber.inclusion
          (pseudofunctor (K.toPseudofunctor.comp F) R) a).map f) =
      (Quillen.CategoryTheory.GrothendieckFiber.inclusion
        ((Under.forget R ⋙ K).toPseudofunctor.comp F) a).map f := by
  have h := Pseudofunctor.Grothendieck.Hom.congr
    ((rebracket K F R).map_id
      (⟨a, x⟩ : Pseudofunctor.Grothendieck (pseudofunctor (K.toPseudofunctor.comp F) R)))
  simp only [rebracket, Pseudofunctor.Grothendieck.categoryStruct_id_fiber,
    eqToHom_refl, Category.id_comp] at h
  refine Pseudofunctor.Grothendieck.Hom.ext _ _ ?_ ?_
  · rfl
  simpa only [rebracket, Quillen.CategoryTheory.GrothendieckFiber.inclusion,
    eqToHom_refl, Category.id_comp] using congrArg (fun k => k ≫ f) h

end Quillen.CategoryTheory.GrothendieckUnderComposition
