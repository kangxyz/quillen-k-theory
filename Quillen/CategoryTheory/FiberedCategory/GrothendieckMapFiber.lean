/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.FiberedCategory.GrothendieckFiberMap

/-!
# Original vertical fibers under a pseudonatural Grothendieck map

The actual total-category map restricts to the original pseudonatural component on each
vertical fiber. The equation retains, and cancels by its proved identity law, the original
pseudonaturality unit comparison. The concrete fiber inverse also recovers every unchanged
vertical map after its original inclusion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckFiber
variable {C : Type u} [Category.{v} C]
    {F G : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}}

/-- The actual Grothendieck map preserves each original vertical inclusion component. -/
theorem map_inclusion (α : Pseudofunctor.StrongTrans F G) (R : C) {x y : F.obj ⟨R⟩} (f : x ⟶ y) :
    (Pseudofunctor.Grothendieck.map α).map ((inclusion F R).map f) =
      (inclusion G R).map ((α.app ⟨R⟩).toFunctor.map f) := by
  have h := Pseudofunctor.Grothendieck.Hom.congr
    ((Pseudofunctor.Grothendieck.map α).map_id
      (⟨R, x⟩ : Pseudofunctor.Grothendieck F))
  simp only [Pseudofunctor.Grothendieck.map,
    Pseudofunctor.Grothendieck.categoryStruct_id_fiber,
    Pseudofunctor.Grothendieck.categoryStruct_id_base,
    eqToHom_refl, Category.id_comp] at h
  refine Pseudofunctor.Grothendieck.Hom.ext _ _ ?_ ?_
  · rfl
  simpa only [Pseudofunctor.Grothendieck.map, inclusion, Functor.map_comp,
    Category.assoc, eqToHom_refl, Category.id_comp] using
    congrArg (fun k => k ≫ (α.app ⟨R⟩).toFunctor.map f) h

/-- The specified concrete fiber inverse recovers the unchanged original vertical map. -/
theorem fromFiber_map_toFiber_map (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
    (R : C) {x y : F.obj ⟨R⟩} (f : x ⟶ y) :
    (fromFiber F R).map ((toFiber F R).map f) = f := by
  apply (toFiber F R).map_injective
  have h := toFiber_map_fromFiber_map F ((toFiber F R).map f)
  change _ = 𝟙 _ ≫ (toFiber F R).map f ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

end Quillen.CategoryTheory.GrothendieckFiber
