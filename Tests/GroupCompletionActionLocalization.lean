/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.GroupCompletion.DiagonalAction
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Regression tests for Grayson's action category

The discrete additive monoid of natural numbers gives genuine translation
arrows between pairs. The tests compose distinct translations, rule out a
reverse arrow, and verify the invariant difference of the two coordinates.
They also exercise the initial unit in the single-coordinate action category.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Quillen.GroupCompletion

namespace Tests.GroupCompletionActionLocalization

local instance : MonoidalCategory (Discrete ℕ) := Discrete.addMonoidal ℕ

/-- The pair `(a, b)` in the diagonal action category. -/
def point (a b : ℕ) : Localization (Discrete ℕ) (Discrete ℕ) :=
  ⟨(Discrete.mk a, Discrete.mk b)⟩

/-- Translate both coordinates by the specified natural number. -/
def step (n a b : ℕ) : point a b ⟶ point (n + a) (n + b) :=
  Localization.mkHom (Discrete.mk n) (eqToHom rfl) (eqToHom rfl)

example : Nonempty (point 2 1 ⟶ point 5 4) := ⟨step 3 2 1⟩

example : step 3 2 1 ≫ step 2 5 4 = step 5 2 1 := by
  apply Quotient.sound
  refine ⟨Iso.refl _, ?_⟩
  exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

example : ¬ Nonempty (point 5 4 ⟶ point 2 1) := by
  rintro ⟨f⟩
  induction f using Quotient.inductionOn with
  | _ f =>
    have h := Discrete.eq_of_hom f.map.1
    change f.denom.as + 5 = 2 at h
    omega

example {a b c d : ℕ} (f : point a b ⟶ point c d) :
    (a : ℤ) - b = (c : ℤ) - d := by
  induction f using Quotient.inductionOn with
  | _ f =>
    have h₁ := Discrete.eq_of_hom f.map.1
    have h₂ := Discrete.eq_of_hom f.map.2
    change f.denom.as + a = c at h₁
    change f.denom.as + b = d at h₂
    omega

example (n : ℕ)
    (f g : (⟨𝟙_ (Discrete ℕ)⟩ : ActionLocalization (Discrete ℕ) (Discrete ℕ)) ⟶
      ⟨Discrete.mk n⟩) : f = g :=
  ActionLocalization.selfUnitIsInitial.hom_ext f g

example (n : ℕ) :
    Nonempty ((⟨𝟙_ (Discrete ℕ)⟩ : ActionLocalization (Discrete ℕ) (Discrete ℕ)) ⟶
      ⟨Discrete.mk n⟩) := ⟨ActionLocalization.selfUnitIsInitial.to _⟩

end Tests.GroupCompletionActionLocalization
