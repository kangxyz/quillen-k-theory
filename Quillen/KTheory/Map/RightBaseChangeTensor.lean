/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveTensorBaseChangeExact
public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
public import Quillen.KTheory.Map.NaturalIso

/-!
# Literal tensor extension gives the original K-map

The canonical natural isomorphism identifies tensor extension with the unchanged
matrix-image exact functor. Natural-isomorphism invariance compares the original
zero-normalized K-maps in every degree. Both rings have a common universe, as
required by the existing K-map interface; no mixed-universe identification of
finite-projective categories is asserted.
-/

@[expose] public section

noncomputable section

universe u

namespace Quillen.FiniteProjectiveModule

variable {R S : Type u} [Ring R] [Ring S]

/-- Literal tensor scalar extension induces the original K-map in every degree. -/
theorem rightTensorBaseChangeExact_KMap (f : R →+* S) (n : ℕ) :
    (rightTensorBaseChangeExact f).KMap n = (rightBaseChangeExact f).KMap n :=
  CategoryTheory.ExactCategory.ExactFunctor.KMap_eq_of_natIso (F := rightTensorBaseChangeExact f)
    (G := rightBaseChangeExact f) (rightTensorBaseChangeIso f) n

end Quillen.FiniteProjectiveModule
