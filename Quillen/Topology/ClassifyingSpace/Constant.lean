/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.Constant

/-! # Constant maps and geometric realization -/
@[expose] public section


noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial

namespace Quillen

/-- The nerve map of a constant functor is the constant simplicial map. -/
theorem nerveMap_const {C D : Type u} [Category.{v} C] [Category.{v} D] (d : D) :
    CategoryTheory.nerveMap ((Functor.const C).obj d) = SSet.const (nerveVertex d) := by
  rfl

/-- A constant functor induces a constant continuous map of classifying spaces. -/
@[simp]
theorem classifyingSpaceMap_const_direct {C D : Type u} [Category.{v} C] [Category.{v} D]
    (d : D) : classifyingSpaceMap ((Functor.const C).obj d) =
      TopCat.const (X := ClassifyingSpace C) (classifyingSpacePoint d) := by
  ext p
  exact realization_const_apply (nerveVertex d) p

end Quillen
