/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Comma.StructuredUniverseLift
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
