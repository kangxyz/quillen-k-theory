/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.SubdivisionAction
public import Quillen.CategoryTheory.GroupCompletion.Functoriality
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Tests for the subdivision action

The component tests retain arbitrary actor morphisms, including their actual
inverses. The discrete natural-number consumer checks a nontrivial object action.
The codomain projection also descends to the actual Grayson localization.
-/

@[expose] public section

noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory Quillen
open scoped MonoidalLeftAction

namespace Tests.SubdivisionAction

section General
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

example {s t : C} (f : s ⟶ t) {X Y : Subdivision D} (g : X ⟶ Y) :
    Subdivision.domainMap (f ⊙ₗₘ g) = inv f ⊙ₗₘ Subdivision.domainMap g := rfl

example {s t : C} (f : s ⟶ t) {X Y : Subdivision D} (g : X ⟶ Y) :
    (f ⊙ₗₘ g).base = f ⊙ₗₘ g.base := rfl

example (s t : C) (X : Subdivision D) :
    Subdivision.domainMap (αₗ s t X).hom = (αₗ s t X.fiber.unop.left).inv := rfl

example (X : Subdivision D) :
    Subdivision.domainMap (λₗ[C] X).hom = (λₗ[C] X.fiber.unop.left).inv := rfl

/-- The actual projection of action localizations uses the identity lineator. -/
def localizedCodomain :
    GroupCompletion.ActionLocalization C (Subdivision D) ⥤
      GroupCompletion.ActionLocalization C D :=
  GroupCompletion.ActionLocalization.mapFunctor (Subdivision.codomain (C := D))

example (X : GroupCompletion.ActionLocalization C (Subdivision D)) :
    (localizedCodomain.obj X).obj = X.obj.base := rfl

end General

local instance : MonoidalCategory (Discrete ℕ) := Discrete.addMonoidal ℕ

/-- A genuine object in the subdivision of the discrete additive monoid. -/
def point (n : ℕ) : Subdivision (Discrete ℕ) := Subdivision.of (𝟙 (Discrete.mk n))

example : ((Discrete.mk 2) ⊙ₗ point 3).base = Discrete.mk 5 := rfl

example : (Discrete.mk 2) ⊴ₗ 𝟙 (point 3) = 𝟙 ((Discrete.mk 2) ⊙ₗ point 3) := by simp

example : Subdivision.domainMap ((λₗ[Discrete ℕ] (point 3)).hom) =
    (λₗ[Discrete ℕ] (Discrete.mk 3)).inv := rfl

end Tests.SubdivisionAction
