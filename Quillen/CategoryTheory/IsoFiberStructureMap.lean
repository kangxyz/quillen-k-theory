/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.IsoFiber

/-! # The specified structure isomorphisms of an isomorphism fiber -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory
namespace Quillen.IsoFiber
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (b : D)

/-- The actual stored structure maps assemble into a natural isomorphism. -/
def structureIso : (Functor.const (IsoFiber F b)).obj b ≅ forget F b ⋙ F :=
  NatIso.ofComponents (fun (X : IsoFiber F b) ↦
    letI : IsIso X.obj.hom := X.property
    asIso X.obj.hom) (fun {X Y} f ↦ by
    change 𝟙 b ≫ Y.obj.hom = X.obj.hom ≫ F.map f.hom.right
    simpa only [Category.id_comp] using (StructuredArrow.w f.hom).symm)

@[simp]
lemma structureIso_hom_app (X : IsoFiber F b) :
    (structureIso F b).hom.app X = X.obj.hom := rfl

/-- Lifting preserves the original functor after forgetting the structure isomorphism. -/
@[simp]
lemma lift_forget {A : Type*} [Category* A] (G : A ⥤ C)
    (e : (Functor.const A).obj b ≅ G ⋙ F) : lift F b G e ⋙ forget F b = G := rfl

/-- The structure map of a lifted object is precisely the supplied original comparison. -/
lemma lift_structureIso_hom_app {A : Type*} [Category* A] (G : A ⥤ C)
    (e : (Functor.const A).obj b ≅ G ⋙ F) (X : A) :
    (structureIso F b).hom.app ((lift F b G e).obj X) = e.hom.app X := rfl

end Quillen.IsoFiber
