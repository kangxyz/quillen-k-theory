/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Simplicial cylinders preserve colimits

Taking the product with a fixed simplicial set preserves colimits, computed
pointwise in types. The pointwise proof works in every universe, without
requiring the indexing category and value category to have equal universes.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

universe u w w'

namespace Quillen

/-- Pointwise products preserve all diagram shapes for which the type category
has colimits, including diagrams with distinct object and morphism universes. -/
instance simplicialTensorLeft_preservesColimitsOfShape (X : SSet.{u})
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (tensorLeft X) := by
  infer_instance

/-- The corresponding arbitrary-shape preservation result for the interval
on the right. -/
instance simplicialCylinder_preservesColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (tensorRight (Δ[1] : SSet.{u})) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

/-- Product on the left with a fixed simplicial set preserves colimits. -/
instance simplicialTensorLeft_preservesColimits (X : SSet.{u}) :
    PreservesColimits (tensorLeft X) where
  preservesColimitsOfShape := by infer_instance

/-- Product with the simplicial interval preserves arbitrary colimits. -/
instance simplicialCylinder_preservesColimits :
    PreservesColimits (tensorRight (Δ[1] : SSet.{u})) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

end Quillen
