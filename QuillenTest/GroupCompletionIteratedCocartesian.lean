/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.CategoryTheory.GroupCompletion.IteratedCocartesian

/-! # Actual cocartesian lifts through both quotient layers -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
  [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]
attribute [local instance] firstCoordinateLeftAction

example (A : Localization C (Localization C D)) (Y : ActionLocalization C D)
    (g : iteratedSecondProjection.obj A ⟶ Y) :
    ∃ (B : Localization C (Localization C D)) (f : A ⟶ B),
      iteratedSecondProjection.obj B = Y ∧
        iteratedSecondProjection.IsStronglyCocartesian g f :=
  exists_iteratedSecondProjectionLift A Y g

example {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    iteratedSecondProjection.IsStronglyCocartesian
      (iteratedSecondProjection.map (iteratedLift s g A B)) (iteratedLift s g A B) :=
  inferInstance
