/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Whiskering

/-!
# Equality-transport squares with specified whole functor identifications

The two identifications of horizontal composites remain explicit instead of being discharged
by concrete definitional conversion inside a component proof.
The intended upstream owner is `Aglib.CategoryTheory.Functor.EqToHomWhiskerSquare`.
-/
@[expose] public section
open CategoryTheory
universe u v u' v' w z w' z'
namespace CategoryTheory.Functor

/-- Whiskered functor-equality transports commute with the two specified composite identities. -/
theorem eqToHom_whisker_square {A : Type u} [Category.{v} A]
    {A' : Type u'} [Category.{v'} A'] {B : Type w} [Category.{z} B]
    {B' : Type w'} [Category.{z'} B']
    (I : A' ⥤ A) (J : B' ⥤ B) (F G : A' ⥤ B') (F' G' : A ⥤ B)
    (h : F = G) (h' : F' = G')
    (l : F ⋙ J = I ⋙ F') (r : G ⋙ J = I ⋙ G') :
    whiskerRight (eqToHom h) J ≫ eqToHom r =
      eqToHom l ≫ whiskerLeft I (eqToHom h') := by
  cases h
  cases h'
  simp only [eqToHom_refl, Functor.whiskerRight_id', Functor.whiskerLeft_id',
    Category.id_comp, Category.comp_id]

end CategoryTheory.Functor
