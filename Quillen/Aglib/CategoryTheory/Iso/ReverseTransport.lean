/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Reversing an isomorphism after equality transport

Transporting the target and then reversing retains the original isomorphism and equality.
This identity also provides an opaque boundary for comparisons with large dependent endpoints.
-/
@[expose] public section
namespace CategoryTheory.Iso

/-- Reverse a target-transported isomorphism using the same original equality and inverse. -/
theorem eqToIso_trans_symm {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (h : D = B) :
    eqToIso h ≪≫ e.symm = (e ≪≫ eqToIso h.symm).symm := by
  subst h
  rfl

end CategoryTheory.Iso
