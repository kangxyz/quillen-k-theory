/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.CategoryTheory.GroupCompletion.MonoidalFunctorNaturality

/-! # Original completion functor coherence consumers -/
noncomputable section
open CategoryTheory MonoidalCategory Quillen.GroupCompletion
universe u v w z u' v'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type w} [Category.{z} D] [MonoidalCategory D]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]

example : monoidalMap (𝟭 C) = 𝟭 (Localization C C) := monoidalMap_id

example (F : C ⥤ D) [F.Monoidal] (G : D ⥤ E) [G.Monoidal] :
    monoidalMap F ⋙ monoidalMap G = monoidalMap (F ⋙ G) := monoidalMap_comp F G

example {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ≅ G)
    [e.hom.IsMonoidal] (X : Localization C C) :
    (monoidalMapIso e).hom.app X =
      ActionLocalization.ofHom (C := D)
        (X := (F.obj X.obj.1, F.obj X.obj.2))
        (Y := (G.obj X.obj.1, G.obj X.obj.2))
        ((e.app X.obj.1).hom, (e.app X.obj.2).hom) := rfl

example (F : C ⥤ D) [F.Monoidal] {X Y : C × C} (f : X ⟶ Y) :
    (monoidalMap F).map (ActionLocalization.ofHom (C := C) f) =
      ActionLocalization.ofHom (C := D) ((F.prod F).map f) := monoidalMap_ofHom F f
