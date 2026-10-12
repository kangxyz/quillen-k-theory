/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.GroupCompletion.ProjectionComma
public import Quillen.CategoryTheory.TheoremA.ContractibleComma
public import Quillen.Topology.ClassifyingSpace.Equivalence

/-!
# Contractible acted-on categories stay contractible under Grayson's localization

The comma category of the actual projection `C⁻¹D ⥤ ⟨C,C⟩` has an
explicit adjunction with `D`. Quillen's already-proved Theorem A therefore
applies when `BD` is contractible. The target has an initial unit object.
No plus-construction, homology, or group-completion theorem is assumed.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [MonoidalCategory C] [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  [MonoidalLeftAction C D]

/-- The actual comma transport and fiber entry realize to inverse homotopy maps. -/
def commaClassifyingHomotopyEquiv (B : C) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow (projection (D := D)) ⟨B⟩))
      (ClassifyingSpace D) :=
  adjunctionClassifyingHomotopyEquiv (commaTransportAdjunction B)

@[simp]
lemma commaClassifyingHomotopyEquiv_toFun (B : C) :
    (commaClassifyingHomotopyEquiv (D := D) B).toFun =
      (classifyingSpaceMap (commaTransport B)).hom := rfl

/-- The projection is an actual homotopy equivalence when the acted-on
classifying space is contractible. -/
def projectionClassifyingHomotopyEquiv [ContractibleSpace (ClassifyingSpace D)] :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C D))
      (ClassifyingSpace (ActionLocalization C C)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv projection
    (fun B ↦ (commaClassifyingHomotopyEquiv B.obj).contractibleSpace)

@[simp]
lemma projectionClassifyingHomotopyEquiv_toFun [ContractibleSpace (ClassifyingSpace D)] :
    (projectionClassifyingHomotopyEquiv (C := C) (D := D)).toFun =
      (classifyingSpaceMap projection).hom := rfl

/-- Grayson's actual localization of a contractible category is contractible. -/
theorem classifyingSpace_contractible [ContractibleSpace (ClassifyingSpace D)] :
    ContractibleSpace (ClassifyingSpace (Localization C D)) := by
  let : ContractibleSpace (ClassifyingSpace (ActionLocalization C C)) :=
    classifyingSpace_contractible_of_isInitial
      (ActionLocalization.selfUnitIsInitial (C := C))
  exact (projectionClassifyingHomotopyEquiv (C := C) (D := D)).contractibleSpace

end Quillen.GroupCompletion.Localization
