/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Whiskering

/-! Whole-isomorphism whiskering along a specified equality of source functors. -/
@[expose] public section
open CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂
namespace CategoryTheory.Functor
variable {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B]
  {C : Type u₂} [Category.{v₂} C]

/-- A whole functor equality transports a whiskered isomorphism before taking components. -/
theorem isoWhiskerLeft_eqToIso_square {F G : A ⥤ B} (h : F = G)
    {P Q : B ⥤ C} (e : P ≅ Q) :
    isoWhiskerLeft F e ≪≫ eqToIso (congrArg (fun H => H ⋙ Q) h) =
      eqToIso (congrArg (fun H => H ⋙ P) h) ≪≫ isoWhiskerLeft G e := by
  cases h
  simp

end CategoryTheory.Functor
