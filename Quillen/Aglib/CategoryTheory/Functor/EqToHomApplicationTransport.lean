/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.EqToHomTransport

/-!
# Opaque component transport for equal functors

Equality of functors gives componentwise equality transport independently of the chosen
proof of the endpoint equality. The corresponding mapped identity keeps both proofs opaque.
The intended upstream owner is `Aglib.CategoryTheory.Functor.EqToHomApplicationTransport`.
-/
@[expose] public section
open CategoryTheory
universe u v u' v' u'' v''
namespace CategoryTheory.Functor
variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
  {C : Type u''} [Category.{v''} C] {F G : A ⥤ B}

/-- A component of functor equality is transport along any proof of its object equality. -/
theorem eqToHom_app_of_eq (h : F = G) (X : A) (h' : F.obj X = G.obj X) :
    (eqToHom h).app X = eqToHom h' := by
  cases h
  rfl

/-- A mapped component of functor equality retains any given proof of its image endpoints. -/
theorem map_eqToHom_app_of_eq (H : B ⥤ C) (h : F = G) (X : A)
    (h' : H.obj (F.obj X) = H.obj (G.obj X)) :
    H.map ((eqToHom h).app X) = eqToHom h' := by
  cases h
  exact H.map_id (F.obj X)

end CategoryTheory.Functor
