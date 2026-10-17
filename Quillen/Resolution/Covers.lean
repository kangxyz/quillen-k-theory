/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.ExactCategory.Resolution.Covers
public import Quillen.Resolution.QCalculus
public import Quillen.Topology.ClassifyingSpace.Equivalence

/-! # Classifying-space contraction of admissible cover refinements -/
@[expose] public section
open CategoryTheory.ExactCategory
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Resolution
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C) (M : C)

namespace Cover
variable {E P M}
variable [E.IsExtensionClosed P] [E.IsAdmissibleSubobjectClosed P]

/-- The category of covers is genuinely contractible: its identity is joined
to a constant by the explicit pullback-refinement zigzag. -/
theorem contractible (B : Cover E P M) :
    ContractibleSpace (ClassifyingSpace (Cover E P M)) := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨classifyingSpacePoint B, ?_⟩
  have h₁ := (classifyingSpaceNaturalTransformationHomotopy (refinementToId B)).symm
  have h₂ := classifyingSpaceNaturalTransformationHomotopy (refinementToConst B)
  simpa only [classifyingSpaceMap_id, TopCat.hom_id, classifyingSpaceMap_const] using
    (ContinuousMap.Homotopic.trans ⟨h₁⟩ ⟨h₂⟩)

end Cover
end Quillen.Resolution
