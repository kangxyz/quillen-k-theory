/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Fibration.RelativeRows.RealizationLifting
public import Quillen.Topology.CubicalSubdivision.FiberBoundaryLifting

/-! # Original relative-row comparison: actual whole-boundary cubical lifting -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)

/-- Every literal finite cube-boundary square lifts for the unchanged actual
normalized row comparison endpoint. All fiber hypotheses are derived from N. -/
theorem rowNormalizedComparison_endpoint_boundaryLifting :
    CubicalSubdivision.BoundaryLifting (MappingPath.endpoint (rowNormalizedComparison N α)) :=
  MappingPath.strictComparison_endpoint_boundaryLifting
    (SSet.toTop.map ((relativeSRows N).map α)).hom
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
    (rowTransitionSquare N α) (fun b ↦ rowTransitionFiberAt_compactHELP N α b)

end Quillen.Waldhausen.Fibration.RelativeRows
