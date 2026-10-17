/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Comma.UniverseLift
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
