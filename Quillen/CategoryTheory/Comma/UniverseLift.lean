/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.UniverseLift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Universe lifting of the original comma projection and transitions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u₁ v₁ u₂ v₂ w
namespace Quillen

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The given functor with both categorical universes lifted. -/
def universeLiftFunctor (F : C ⥤ D) : AsSmall.{w} C ⥤ AsSmall.{w} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- Lift an original costructured arrow, retaining its original arrow. -/
def costructuredArrowUniverseUp (F : C ⥤ D) (d : D) :
    CostructuredArrow F d ⥤
      CostructuredArrow (universeLiftFunctor.{u₁, v₁, u₂, v₂, w} F) (AsSmall.up.obj d) where
  obj x := CostructuredArrow.mk (Y := AsSmall.up.obj x.left) ⟨x.hom⟩
  map f := CostructuredArrow.homMk ⟨f.left⟩ (by
    apply ULift.ext
    exact CostructuredArrow.w f)

/-- Lower a lifted costructured arrow without changing its arrow. -/
def costructuredArrowUniverseDown (F : C ⥤ D) (d : D) :
    CostructuredArrow (universeLiftFunctor.{u₁, v₁, u₂, v₂, w} F) (AsSmall.up.obj d) ⥤
      CostructuredArrow F d where
  obj x := CostructuredArrow.mk (Y := ULift.down x.left) x.hom.down
  map f := CostructuredArrow.homMk f.left.down (by
    exact congrArg ULift.down (CostructuredArrow.w f))

@[simp] theorem costructuredArrowUniverseUp_down (F : C ⥤ D) (d : D) :
    costructuredArrowUniverseUp.{u₁, v₁, u₂, v₂, w} F d ⋙
      costructuredArrowUniverseDown F d = 𝟭 _ := rfl

@[simp] theorem costructuredArrowUniverseDown_up (F : C ⥤ D) (d : D) :
    costructuredArrowUniverseDown.{u₁, v₁, u₂, v₂, w} F d ⋙
      costructuredArrowUniverseUp F d = 𝟭 _ := rfl

/-- The categorical lift is strictly compatible with the original comma projection. -/
theorem costructuredArrowUniverseUp_proj (F : C ⥤ D) (d : D) :
    costructuredArrowUniverseUp.{u₁, v₁, u₂, v₂, w} F d ⋙
        CostructuredArrow.proj (universeLiftFunctor F) (AsSmall.up.obj d) =
      CostructuredArrow.proj F d ⋙ AsSmall.up := rfl

/-- Lifting commutes strictly with each original comma transition. -/
theorem costructuredArrowUniverseUp_map (F : C ⥤ D) {d e : D} (f : d ⟶ e) :
    costructuredArrowUniverseUp.{u₁, v₁, u₂, v₂, w} F d ⋙
        CostructuredArrow.map (AsSmall.up.map f) =
      CostructuredArrow.map f ⋙ costructuredArrowUniverseUp F e := rfl

/-- Original comma classifying spaces are homeomorphic to their lifted counterparts. -/
def costructuredArrowUniverseHomeomorph (F : C ⥤ D) (d : D) :
    ClassifyingSpace (CostructuredArrow F d) ≃ₜ
      ClassifyingSpace (CostructuredArrow
        (universeLiftFunctor.{u₁, v₁, u₂, v₂, w} F) (AsSmall.up.obj d)) where
  toFun := classifyingSpaceMapUniversal (costructuredArrowUniverseUp F d)
  invFun := classifyingSpaceMapUniversal (costructuredArrowUniverseDown F d)
  left_inv x := by
    change ((classifyingSpaceMapUniversal (costructuredArrowUniverseDown F d)).comp
      (classifyingSpaceMapUniversal (costructuredArrowUniverseUp F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, costructuredArrowUniverseUp_down,
      classifyingSpaceMapUniversal_id]
    rfl
  right_inv x := by
    change ((classifyingSpaceMapUniversal (costructuredArrowUniverseUp F d)).comp
      (classifyingSpaceMapUniversal (costructuredArrowUniverseDown F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, costructuredArrowUniverseDown_up,
      classifyingSpaceMapUniversal_id]
    rfl
  continuous_toFun := (classifyingSpaceMapUniversal (costructuredArrowUniverseUp F d)).continuous
  continuous_invFun := (classifyingSpaceMapUniversal (costructuredArrowUniverseDown F d)).continuous

end Quillen
