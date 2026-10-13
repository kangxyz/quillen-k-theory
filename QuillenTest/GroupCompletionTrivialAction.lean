/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.TrivialAction
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# QuillenTest for the trivial action and its forgetful functor

The discrete additive monoid of natural numbers acts trivially on the terminal
discrete category. Its action category still has distinct translation loops.
The forgetful functor preserves composition and sends every such loop to the
identity, so it is not faithful in this example.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Quillen.GroupCompletion

namespace QuillenTest.GroupCompletionTrivialAction

local instance : MonoidalCategory (Discrete ℕ) := Discrete.addMonoidal ℕ
local instance : MonoidalLeftAction (Discrete ℕ) (Discrete PUnit) :=
  MonoidalLeftAction.trivial _ _

/-- The unique object of this action category. -/
def point : ActionLocalization (Discrete ℕ) (Discrete PUnit) :=
  ⟨Discrete.mk PUnit.unit⟩

/-- A translation loop with a specified natural-number denominator. -/
def loop (n : ℕ) : point ⟶ point :=
  ActionLocalization.mkHom ⟨Discrete.mk n, 𝟙 _⟩

example (m n : ℕ) : loop m ≫ loop n = loop (n + m) := by
  apply Quotient.sound
  refine ⟨Iso.refl _, ?_⟩
  exact Subsingleton.elim _ _

/-- Denominators are retained even though the action is trivial. -/
theorem loop_eq_iff (m n : ℕ) : loop m = loop n ↔ m = n := by
  change ActionLocalization.mkHom _ = ActionLocalization.mkHom _ ↔ m = n
  rw [ActionLocalization.mkHom_eq_iff, ActionLocalization.TrivialAction.rel_iff]
  constructor
  · rintro ⟨⟨e⟩, _⟩
    exact Discrete.eq_of_hom e.hom
  · rintro rfl
    exact ⟨⟨Iso.refl _⟩, rfl⟩

example (n : ℕ) :
    (ActionLocalization.TrivialAction.forgetFunctor (Discrete ℕ) (Discrete PUnit)).map
      (loop n) = 𝟙 (Discrete.mk PUnit.unit) := rfl

example : loop 0 ≠ loop 1 := by simp [loop_eq_iff]

example :
    ¬ (ActionLocalization.TrivialAction.forgetFunctor
      (Discrete ℕ) (Discrete PUnit)).Faithful := by
  intro h
  have he : loop 0 = loop 1 := h.map_injective rfl
  exact (by simp [loop_eq_iff] : loop 0 ≠ loop 1) he

end QuillenTest.GroupCompletionTrivialAction
