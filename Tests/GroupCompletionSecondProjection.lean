/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.GroupCompletion.SecondProjectionCocartesian

/-! # The actual second projection, its fibers, and cocartesian lifts -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
  [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]

example (X : D) : C ≌ Functor.Fiber (secondProjection (C := C)) ⟨X⟩ :=
  secondFiberEquivalence X

example (A : Localization C D) (Y : ActionLocalization C D)
    (g : secondProjection.obj A ⟶ Y) :
    ∃ (B : Localization C D) (f : A ⟶ B),
      secondProjection.obj B = Y ∧
        secondProjection.IsStronglyCocartesian g f :=
  exists_secondProjectionLift A Y g

example {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) {A B : C} (f : A ⟶ B) :
    secondFiberHom X f ≫ secondLift s g B =
      secondLift s g A ≫ secondFiberHom Y (s ◁ f) :=
  secondLift_naturality s g f
