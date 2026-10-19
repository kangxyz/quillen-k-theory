/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Components of equality transport after functor composition

Keep the original functor equality opaque when applying a further evaluation functor.
The intended upstream owner is `Aglib.CategoryTheory.Functor.EqToHomWhiskering`.
-/
@[expose] public section
open CategoryTheory
universe u v u' v' u'' v''
namespace CategoryTheory.Functor

/-- Postcomposition carries a functor-equality component to its actual mapped component. -/
theorem eqToHom_comp_app {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] {C : Type u''} [Category.{v''} C]
    (E : B ⥤ C) {F G : A ⥤ B} (h : F = G) (X : A) :
    (eqToHom (congrArg (fun H => H ⋙ E) h)).app X = E.map ((eqToHom h).app X) := by
  cases h
  exact (E.map_id (F.obj X)).symm

end CategoryTheory.Functor
