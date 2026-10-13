/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.CylinderAttachment.Overlap

/-! Regression tests for attachment of both ends to the same base. In particular,
the collar chart remains valid when the two attaching maps are identical. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory Topology
open scoped Topology unitInterval
universe u

namespace QuillenTest.CylinderAttachmentGeometry

open Quillen
open CylinderAttachment

variable {A B D : TopCat.{u}} (f₀ f₁ : A ⟶ B)
  {l : A ⊗ TopCat.I ⟶ D} {e : B ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f₀ f₁) l e)

include sq in
/-- A cover by a neighborhood homotopy equivalent to the base and the honest
open cylinder exists for arbitrary endpoint maps into that same base. -/
theorem attachment_openCover : ∃ U V : Set D,
    IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧ Set.range e ⊆ U ∧
      Nonempty (ContinuousMap.HomotopyEquiv B U) ∧
      Nonempty (A × DoubleCylinder.OpenInterval ≃ₜ V) := by
  refine ⟨collarSet f₀ f₁ sq (1 / 3), interiorSet f₀ f₁ sq,
    collar_isOpen f₀ f₁ sq _, interior_isOpen f₀ f₁ sq,
    collar_union_interior f₀ f₁ sq _ (by norm_num), ?_, ?_, ⟨interiorHomeomorph f₀ f₁ sq⟩⟩
  · rintro _ ⟨b, rfl⟩
    change height f₀ f₁ sq (e b) < 1 / 3
    rw [height_base]
    norm_num
  · exact ⟨(collarStrongDeformationRetract (1 / 3) f₀ f₁ sq
      (by norm_num) (by norm_num)).toHomotopyEquiv⟩

/-- Identical attaching maps cause no failure of the collar calculation. -/
theorem identical_endpoints_projection (f : A ⟶ B)
    (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f f) l e)
    (z : A × OverlapInterval (1 / 3)) :
    collarProjection (1 / 3) f f sq (by norm_num) (by norm_num)
      (overlapToCollar f f sq (1 / 3) (overlapHomeomorph f f sq (1 / 3) z)) = f z.1 := by
  rw [collarProjection_overlap]
  exact ite_self _

end QuillenTest.CylinderAttachmentGeometry
