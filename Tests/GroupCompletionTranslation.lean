/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.GroupCompletionTranslation
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Translation regression tests

The discrete additive monoid of natural numbers supplies concrete noninvertible
objects. Its two coordinate translations become inverse homotopy equivalences
on the actual realization of Grayson's category.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Quillen Quillen.GroupCompletion

namespace Tests.GroupCompletionTranslation

local instance : MonoidalCategory (Discrete ℕ) := Discrete.addMonoidal ℕ

local instance : BraidedCategory (Discrete ℕ) where
  braiding X Y := eqToIso (congrArg Discrete.mk (Nat.add_comm X.as Y.as))
  braiding_naturality_left := by intros; apply Subsingleton.elim
  braiding_naturality_right := by intros; apply Subsingleton.elim
  hexagon_forward := by intros; apply Subsingleton.elim
  hexagon_reverse := by intros; apply Subsingleton.elim

/-- The pair of natural numbers regarded as an object of Grayson's category. -/
def point (a b : ℕ) : Localization (Discrete ℕ) (Discrete ℕ) :=
  ⟨Discrete.mk a, Discrete.mk b⟩

example : (Localization.firstTranslation (Discrete.mk 3)).obj (point 2 1) = point 5 1 := rfl

example : (Localization.secondTranslation (Discrete.mk 3)).obj (point 2 1) = point 2 4 := rfl

example : Nonempty (point 2 1 ⟶ point 5 4) :=
  ⟨(Localization.diagonalTranslationNatTrans (Discrete.mk 3)).app (point 2 1)⟩

example (s : Discrete ℕ) :
    (Localization.diagonalTranslationNatTrans s).app ⟨𝟙_ _, 𝟙_ _⟩ ≫
      ActionLocalization.ofHom (C := Discrete ℕ)
        (X := (𝟙_ (Discrete ℕ) ⊗ s, 𝟙_ (Discrete ℕ) ⊗ s)) (Y := (s, s))
        ((λ_ s).hom, (λ_ s).hom) =
        Localization.mkHom (X := (𝟙_ (Discrete ℕ), 𝟙_ (Discrete ℕ)))
          (Y := (s, s)) s (ρ_ s).hom (ρ_ s).hom :=
  Localization.diagonalTranslationNatTrans_unit s

example (s : Discrete ℕ)
    (x : ClassifyingSpace (Localization (Discrete ℕ) (Discrete ℕ))) :
    Localization.translationClassifyingHomotopyEquiv s x =
      classifyingSpaceMap (Localization.firstTranslation s) x := rfl

example (s : Discrete ℕ)
    (x : ClassifyingSpace (Localization (Discrete ℕ) (Discrete ℕ))) :
    (Localization.translationClassifyingHomotopyEquiv s).symm x =
      classifyingSpaceMap (Localization.secondTranslation s) x := rfl

end Tests.GroupCompletionTranslation
