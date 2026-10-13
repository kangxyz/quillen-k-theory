/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.FiberCocartesianComma

/-! # Consumer tests for the actual strict-fiber comma inclusion -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

example (F : C ⥤ D) (b : D)
    (lifts : ∀ U : CostructuredArrow F b,
      ∃ (x : C) (_hx : F.obj x = b) (f : U.left ⟶ x),
        F.IsStronglyCocartesian U.hom f) :
    (Quillen.Fiber.toCostructured F b).IsRightAdjoint := by
  apply Quillen.Fiber.toCostructured_isRightAdjoint_of_lifts
  intro U
  obtain ⟨x, hx, f, hf⟩ := lifts U
  let := hf
  exact ⟨x, hx, f, inferInstance⟩

example (F : C ⥤ D) (b : D) (X : F.Fiber b) :
    ((Quillen.Fiber.toCostructured F b).obj X).hom = eqToHom X.2 := rfl

example (F : C ⥤ D) (b : D) {X Y : F.Fiber b} (f : X ⟶ Y) :
    ((Quillen.Fiber.toCostructured F b).map f).left = f.val := rfl
