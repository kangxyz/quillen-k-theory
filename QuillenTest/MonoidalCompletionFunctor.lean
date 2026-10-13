/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.GroupCompletion.MonoidalFunctor

/-! # Exact common-denominator and unit-entry consumers -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Quillen.GroupCompletion
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type w} [Category.{z} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

example {A B A' B' : C} (s : C) (f : s ⊗ A ⟶ A') (g : s ⊗ B ⟶ B') :
    (monoidalMap F).map (Localization.mkHom (X := (A, B)) (Y := (A', B')) s f g) =
      Localization.mkHom (X := (F.obj A, F.obj B)) (Y := (F.obj A', F.obj B')) (F.obj s)
        (Functor.LaxMonoidal.μ F s A ≫ F.map f)
        (Functor.LaxMonoidal.μ F s B ≫ F.map g) :=
  monoidalMap_mkHom F s f g

example : Localization.unitEntry (C := C) ⋙ monoidalMap F ≅
    F ⋙ Localization.unitEntry (C := D) := monoidalMapUnitIso F
