/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.FullSubcategory.Pushout

/-! # Original pushout arrows under a full-subcategory lift

The consumer retains the canonical source pushout inclusions and derives the
lifted square from preservation of that single source diagram.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace FullSubcategoryLiftPushoutConsumers

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A preserved canonical source pushout retains both original inclusion maps. -/
theorem lifted_canonical_pushout (P : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ X, P (F.obj X)) {A B E : C} (f : A ⟶ B) (g : A ⟶ E)
    [HasPushout f g] [PreservesColimit (span f g) F] :
    IsPushout ((P.lift F hF).map f) ((P.lift F hF).map g)
      ((P.lift F hF).map (pushout.inl f g))
      ((P.lift F hF).map (pushout.inr f g)) :=
  P.isPushout_lift F hF ((IsPushout.of_hasPushout f g).map F)

end FullSubcategoryLiftPushoutConsumers
