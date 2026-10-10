/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.Diagonal
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! The genuine diagonal functor preserves colimits, since each diagonal
    degree is the composite of the two evaluation functors. -/
@[expose] public section


noncomputable section
open CategoryTheory Limits Opposite
universe u v w
namespace Quillen.TheoremA

instance diagonalFunctor_preservesColimits [HasColimitsOfSize.{v, w} (Type u)] :
  PreservesColimitsOfSize.{v, w} diagonalFunctor.{u} := by
  constructor
  intro J _
  apply preservesColimitsOfShape_of_evaluation
  intro p
  change PreservesColimitsOfShape J
    (((evaluation SimplexCategoryᵒᵖ SSet).obj p) ⋙
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj p)
  infer_instance

end Quillen.TheoremA
