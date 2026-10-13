/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.Comma.UniverseLift

/-! # Strict universe lifting of structured arrows

The original structured arrows, their projections, and their precomposition
transitions are retained by the categorical lift and its realized homeomorphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u₁ v₁ u₂ v₂ w
namespace Quillen
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Lift a structured arrow without changing its original component arrow. -/
def structuredArrowUniverseUp (F : C ⥤ D) (d : D) :
    StructuredArrow d F ⥤
      StructuredArrow (AsSmall.up.obj d) (universeLiftFunctor.{u₁, v₁, u₂, v₂, w} F) where
  obj x := StructuredArrow.mk (Y := AsSmall.up.obj x.right) ⟨x.hom⟩
  map f := StructuredArrow.homMk ⟨f.right⟩ (by
    apply ULift.ext
    exact StructuredArrow.w f)

/-- Lower a lifted structured arrow without changing its original component arrow. -/
def structuredArrowUniverseDown (F : C ⥤ D) (d : D) :
    StructuredArrow (AsSmall.up.obj d) (universeLiftFunctor.{u₁, v₁, u₂, v₂, w} F) ⥤
      StructuredArrow d F where
  obj x := StructuredArrow.mk (Y := ULift.down x.right) x.hom.down
  map f := StructuredArrow.homMk f.right.down (by
    exact congrArg ULift.down (StructuredArrow.w f))

@[simp] theorem structuredArrowUniverseUp_down (F : C ⥤ D) (d : D) :
    structuredArrowUniverseUp.{u₁, v₁, u₂, v₂, w} F d ⋙
      structuredArrowUniverseDown F d = 𝟭 _ := rfl

@[simp] theorem structuredArrowUniverseDown_up (F : C ⥤ D) (d : D) :
    structuredArrowUniverseDown.{u₁, v₁, u₂, v₂, w} F d ⋙
      structuredArrowUniverseUp F d = 𝟭 _ := rfl

/-- Lifting preserves the original structured projection strictly. -/
theorem structuredArrowUniverseUp_proj (F : C ⥤ D) (d : D) :
    structuredArrowUniverseUp.{u₁, v₁, u₂, v₂, w} F d ⋙
        StructuredArrow.proj (AsSmall.up.obj d) (universeLiftFunctor F) =
      StructuredArrow.proj d F ⋙ AsSmall.up := rfl

/-- Lifting preserves every original structured transition strictly. -/
theorem structuredArrowUniverseUp_map (F : C ⥤ D) {d e : D} (f : d ⟶ e) :
    structuredArrowUniverseUp.{u₁, v₁, u₂, v₂, w} F e ⋙
        StructuredArrow.map (AsSmall.up.map f) =
      StructuredArrow.map f ⋙ structuredArrowUniverseUp F d := rfl

/-- The structured comma lift is a homeomorphism of the original realizations. -/
def structuredArrowUniverseHomeomorph (F : C ⥤ D) (d : D) :
    ClassifyingSpace (StructuredArrow d F) ≃ₜ
      ClassifyingSpace (StructuredArrow (AsSmall.up.obj d)
        (universeLiftFunctor.{u₁, v₁, u₂, v₂, w} F)) where
  toFun := classifyingSpaceMapUniversal (structuredArrowUniverseUp F d)
  invFun := classifyingSpaceMapUniversal (structuredArrowUniverseDown F d)
  left_inv x := by
    change ((classifyingSpaceMapUniversal (structuredArrowUniverseDown F d)).comp
      (classifyingSpaceMapUniversal (structuredArrowUniverseUp F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, structuredArrowUniverseUp_down,
      classifyingSpaceMapUniversal_id]
    rfl
  right_inv x := by
    change ((classifyingSpaceMapUniversal (structuredArrowUniverseUp F d)).comp
      (classifyingSpaceMapUniversal (structuredArrowUniverseDown F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, structuredArrowUniverseDown_up,
      classifyingSpaceMapUniversal_id]
    rfl
  continuous_toFun := (classifyingSpaceMapUniversal (structuredArrowUniverseUp F d)).continuous
  continuous_invFun := (classifyingSpaceMapUniversal (structuredArrowUniverseDown F d)).continuous

end Quillen
