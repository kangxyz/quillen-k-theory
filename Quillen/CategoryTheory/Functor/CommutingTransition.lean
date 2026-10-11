/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Actual transitions across commuting functor equalities

A specified functor commutation transports an original seed arrow. Naturality of a second
specified commutation identifies its image with the unchanged original transition. All
endpoint transports are retained, including the successor commutation equality.
-/
@[expose] public section
open CategoryTheory
universe u v u' v'
namespace Quillen.Functor
variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- Naturality through two actual commuting functors retains the original seed and its casts. -/
theorem commuting_transition (U : A ⥤ B) (L I : A ⥤ A) (M J : B ⥤ B)
    (h₀ : U ⋙ M = L ⋙ U) (h : U ⋙ J = I ⋙ U)
    (h₁ : U ⋙ (M ⋙ J) = (L ⋙ I) ⋙ U) {X : A} (η : X ⟶ L.obj X) :
    J.map (U.map η ≫ eqToHom (Functor.congr_obj h₀ X).symm) ≫
        eqToHom (Functor.congr_obj h₁ X) =
      eqToHom (Functor.congr_obj h X) ≫ U.map (I.map η) := by
  rw [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans]
  have hn := (eqToHom h).naturality η
  simpa only [eqToHom_app, Functor.comp_obj, Functor.comp_map] using hn

end Quillen.Functor
