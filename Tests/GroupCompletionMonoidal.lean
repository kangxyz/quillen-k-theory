/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.GroupCompletion.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Tests for the actual symmetric multiplication on Grayson's category

The discrete additive monoid of natural numbers has noninvertible objects.
The tests exercise simultaneous tensor multiplication of nonidentity arrows,
the inherited coherence, and the explicit inverse-object arrow.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Quillen.GroupCompletion

namespace Tests.GroupCompletionMonoidal

local instance : MonoidalCategory (Discrete ℕ) := Discrete.addMonoidal ℕ

local instance : SymmetricCategory (Discrete ℕ) where
  braiding X Y := eqToIso (congrArg Discrete.mk (Nat.add_comm X.as Y.as))
  braiding_naturality_left := by intros; apply Subsingleton.elim
  braiding_naturality_right := by intros; apply Subsingleton.elim
  hexagon_forward := by intros; apply Subsingleton.elim
  hexagon_reverse := by intros; apply Subsingleton.elim
  symmetry := by intros; apply Subsingleton.elim

/-- A pair of natural numbers in Grayson's category. -/
def point (a b : ℕ) : Localization (Discrete ℕ) (Discrete ℕ) :=
  ⟨Discrete.mk a, Discrete.mk b⟩

/-- A nonidentity simultaneous translation. -/
def step (n a b : ℕ) : point a b ⟶ point (n + a) (n + b) :=
  Localization.mkHom (Discrete.mk n) (eqToHom rfl) (eqToHom rfl)

example : point 2 1 ⊗ point 3 4 = point 5 5 := rfl

example : step 3 2 1 ⊗ₘ step 2 4 3 = step 5 6 4 := by
  apply Quotient.sound
  refine ⟨Iso.refl _, ?_⟩
  exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

example : Nonempty (point 0 0 ⟶ point 7 7) :=
  ⟨Localization.inverseArrow (point 2 5)⟩

example (X Y : Localization (Discrete ℕ) (Discrete ℕ)) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := SymmetricCategory.symmetry X Y

example {X Y : Discrete ℕ × Discrete ℕ} (f : X ⟶ Y) :
    Localization.tensorHom (ActionLocalization.ofHom (C := Discrete ℕ) f)
      (ActionLocalization.ofHom (C := Discrete ℕ) f) =
      ActionLocalization.ofHom (C := Discrete ℕ)
        (X := Localization.tensorPair X X) (Y := Localization.tensorPair Y Y)
        (f.1 ⊗ₘ f.1, f.2 ⊗ₘ f.2) := Localization.tensorHom_ofHom f f

end Tests.GroupCompletionMonoidal
