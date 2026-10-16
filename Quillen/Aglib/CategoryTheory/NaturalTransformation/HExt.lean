/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Functor.Category

/-! # Heterogeneous equality from actual natural-transformation components -/
@[expose] public section
universe u v
open CategoryTheory
namespace Quillen.Waldhausen.Additivity
variable {D : Type u} [Category.{v} D]

/-- Heterogeneous component equality is enough once the endpoint functors are
identified; this is ordinary extensionality of natural transformations. -/
theorem natTrans_heq_of_app_heq {J : Type u} [Category.{v} J]
    {A A' B B' : J ⥤ D} (η : A ⟶ B) (η' : A' ⟶ B')
    (hA : A = A') (hB : B = B') (hη : ∀ x, HEq (η.app x) (η'.app x)) : HEq η η' := by
  subst A'
  subst B'
  apply heq_of_eq
  ext x
  exact eq_of_heq (hη x)

end Quillen.Waldhausen.Additivity
