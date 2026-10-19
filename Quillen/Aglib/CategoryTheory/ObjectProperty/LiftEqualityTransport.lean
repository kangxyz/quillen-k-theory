/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EqToHom

/-!
# Equality transport through a further full-subcategory lift

The actual inclusion forgets the extra property without changing transport along
an equality of the original functors. The two functor-equality proofs remain independent.
The intended upstream owner is `Aglib.CategoryTheory.ObjectProperty.LiftEqualityTransport`.
-/
@[expose] public section
open CategoryTheory
universe u v u' v'
namespace CategoryTheory.ObjectProperty

/-- Forgetting a further property retains the actual component of original functor equality. -/
theorem ιOfLE_map_lift_eqToHom_app {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (P : ObjectProperty C) (Q R : ObjectProperty D) (hRQ : R ≤ Q)
    (F G : C ⥤ Q.FullSubcategory) (h : F = G)
    (hF : ∀ K : P.FullSubcategory, R (F.obj K.obj).obj)
    (hG : ∀ K : P.FullSubcategory, R (G.obj K.obj).obj)
    (hs : R.lift (P.ι ⋙ F ⋙ Q.ι) hF = R.lift (P.ι ⋙ G ⋙ Q.ι) hG)
    (K : P.FullSubcategory) :
    (ιOfLE hRQ).map ((eqToHom hs).app K) = (eqToHom h).app K.obj := by
  cases h
  rfl

end CategoryTheory.ObjectProperty
