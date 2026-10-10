/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.Realization.Homotopy
import Quillen.Topology.ClassifyingSpace.Basic
import Mathlib.CategoryTheory.Category.ULift

/-!
# An actual nerve isomorphism for common-universe models

Up/down postcomposition is strictly inverse on original nerves. Its realized
homeomorphism preserves the original object vertices, without changing the
maximum realization universe.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.GroupoidClassifying
open scoped Simplicial
variable (C : Type u) [Category.{v} C]

/-- The original nerve is strictly isomorphic to its common-universe lifted nerve. -/
def asSmallNerveIso : nerve C ≅ nerve (AsSmall.{0} C) where
  hom := {
    app _ := ↾fun F ↦ F ⋙ AsSmall.up
    naturality _ _ _ := by ext F; rfl }
  inv := {
    app _ := ↾fun F ↦ F ⋙ AsSmall.down
    naturality _ _ _ := by ext F; rfl }
  hom_inv_id := by ext n F; rfl
  inv_hom_id := by ext n F; rfl

def asSmallClassifyingHomeomorph : ClassifyingSpace C ≃ₜ ClassifyingSpace (AsSmall.{0} C) :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (asSmallNerveIso C))

@[simp] theorem asSmallClassifyingHomeomorph_point (c : C) :
    asSmallClassifyingHomeomorph C (classifyingSpacePoint c) =
      classifyingSpacePoint (AsSmall.up.obj c) := by
  change SSet.toTop.map (asSmallNerveIso C).hom (realizationPoint (nerveVertex c)) = _
  rw [realizationPoint_naturality]
  rfl

end Quillen.GroupoidClassifying
