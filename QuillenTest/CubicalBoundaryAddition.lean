/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.CubicalUpperFaceFold

/-! Named regressions for genuine square folding, actual relative homotopies,
and the multiplication order before any commutativity assumption. -/

@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace QuillenTest.CubicalBoundaryAddition

open Quillen

/-- A moving corner provides a regression against an invalid all-time corner claim. -/
theorem moving_top_left_corner :
    faceFold (⟨1 / 2, by norm_num⟩ : I) (0, 1) =
      (0, (⟨1 / 2, by norm_num⟩ : I)) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    norm_num [faceFold, faceFoldTopX, faceFoldTopY]

/-- The seam of the two chronological top segments is the top-left corner. -/
theorem top_seam : faceFold 1 ((⟨1 / 2, by norm_num⟩ : I), 1) = (0, 1) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    norm_num [faceFold, faceFoldTopX, faceFoldTopY]

/-- Boundary preservation holds at every time, even though corners can move. -/
theorem full_boundary_track (r : I) (p : I × I) (hp : SquareBoundary p) :
    SquareBoundary (faceFold r p) := faceFold_boundary r p hp

variable {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- The degree-one fold already has its specified noncommutative product order. -/
theorem degree_one_lower_order (F : C((Fin 2 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 2), F x = z) :
    cubicalClass (topGenLoop (foldContinuousCube F 0 1)
      (foldContinuousCube_codimTwo F hF 0 1 (by decide))) =
      cubicalClass (topGenLoop F hF) *
        cubicalClass (lateralGenLoop F hF 0 0 (Or.inl rfl)) :=
  topGenLoop_fold_class F hF 0

/-- Reflection yields inverse-upper times top before any commutative rearrangement. -/
theorem degree_one_upper_order (F : C((Fin 2 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 2), F x = z) :
    cubicalClass (topGenLoop (foldUpperContinuousCube F 0 1)
      (foldUpperContinuousCube_codimTwo F hF 0 1 (by decide))) =
      (cubicalClass (lateralGenLoop F hF 0 1 (Or.inr rfl)))⁻¹ *
        cubicalClass (topGenLoop F hF) :=
  topGenLoop_upperFold_class F hF 0

/-- In a three-cube, a different face has a complete boundary-relative lower-fold homotopy. -/
def lower_other_face_track (F : C((Fin 3 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 3), F x = z) :
    (cubicalSphericalFace F hF 2 0 (Or.inl rfl)).val.HomotopyRel
      (cubicalSphericalFace (foldContinuousCube F 0 1)
        (foldContinuousCube_codimTwo F hF 0 1 (by decide)) 2 0 (Or.inl rfl)).val
      (_root_.Cube.boundary (Fin 2)) :=
  otherFaceFoldHomotopy F hF 0 1 2 (by decide) (by decide) (by decide) 0 (Or.inl rfl)

/-- The reflected fold retains the corresponding full relative homotopy as well. -/
def upper_other_face_track (F : C((Fin 3 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 3), F x = z) :
    (cubicalSphericalFace F hF 2 1 (Or.inr rfl)).val.HomotopyRel
      (cubicalSphericalFace (foldUpperContinuousCube F 0 1)
        (foldUpperContinuousCube_codimTwo F hF 0 1 (by decide)) 2 1 (Or.inr rfl)).val
      (_root_.Cube.boundary (Fin 2)) :=
  otherFaceUpperFoldHomotopy F hF 0 1 2 (by decide) (by decide) (by decide) 1 (Or.inr rfl)

/-- Both terminal folds preserve the actual codimension-two basedness condition. -/
theorem terminal_codimTwo (F : C((Fin 3 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 3), F x = z)
    (x : Fin 3 → I) (hx : x ∈ cubeCodimTwoBoundary (Fin 3)) :
    foldContinuousCube F 0 1 x = z ∧ foldUpperContinuousCube F 0 1 x = z :=
  ⟨foldContinuousCube_codimTwo F hF 0 1 (by decide) x hx,
    foldUpperContinuousCube_codimTwo F hF 0 1 (by decide) x hx⟩

end QuillenTest.CubicalBoundaryAddition
