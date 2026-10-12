/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.GroupCompletion.IteratedComma
public import Quillen.CategoryTheory.FiberCocartesianComma

/-! # The genuine strict-fiber/comma adjunction for the iterated projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The explicit group-completion entry factors through the genuine strict fiber. -/
theorem iteratedCommaEntry_factorization (X : D) :
    iteratedStrictFiberEntry X ⋙
      Quillen.Fiber.toCostructured (iteratedSecondProjection (C := C)) ⟨X⟩ =
        iteratedCommaEntry X := rfl

variable [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]

instance iteratedFiberInclusion_isRightAdjoint (b : ActionLocalization C D) :
    (Quillen.Fiber.toCostructured iteratedSecondProjection b).IsRightAdjoint := by
  apply Quillen.Fiber.toCostructured_isRightAdjoint_of_lifts
  intro U
  obtain ⟨x, f, hx, hf⟩ := exists_iteratedSecondProjectionLift U.left b U.hom
  let := hf
  exact ⟨x, hx, f, inferInstance⟩

/-- Cocartesian lifting supplies the actual left adjoint to the fiber inclusion. -/
def iteratedFiberCommaAdjunction (b : ActionLocalization C D) :
    Functor.leftAdjoint (Quillen.Fiber.toCostructured iteratedSecondProjection b) ⊣
      Quillen.Fiber.toCostructured iteratedSecondProjection b :=
  Adjunction.ofIsRightAdjoint _

end Quillen.GroupCompletion.Localization
