/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Functorial equality transport with independently supplied endpoint proofs

This form keeps both equality proofs opaque when applying the identity to large geometric
functors. The intended upstream owner is `Aglib.CategoryTheory.Functor.EqToHomTransport`.
-/
@[expose] public section
open CategoryTheory
universe u v u' v'
namespace CategoryTheory.Functor

/-- A functor preserves equality transport for any proof of the equality of image endpoints. -/
theorem map_eqToHom_of_eq {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {X Y : C}
    (h : X = Y) (h' : F.obj X = F.obj Y) :
    F.map (eqToHom h) = eqToHom h' := by
  cases h
  exact F.map_id X

end CategoryTheory.Functor
