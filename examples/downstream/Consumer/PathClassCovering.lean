/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.LocalConnectorHypotheses
public import Mathlib.Topology.Homotopy.Lifting

/-! Independent named client on the literal chart-generated total space. -/
@[expose] public section
noncomputable section
open scoped unitInterval
universe u
namespace Quillen.Consumer
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

/-- An actual connector on a pathconnected space constructs a surjective
covering without assuming local path connectedness or a cover in the input. -/
theorem covering_from_actual_connector (E : LocalEquiconnection X) (b : X) :
    letI := E.locallyPathConnectedSpace
    letI := (E.pathThinNeighborhoods.prebundle b).totalSpaceTopology
    IsCoveringMap (Bundle.TotalSpace.proj : PathThinNeighborhoods.Total b → X) ∧
      Function.Surjective (Bundle.TotalSpace.proj : PathThinNeighborhoods.Total b → X) := by
  let := E.locallyPathConnectedSpace
  let := (E.pathThinNeighborhoods.prebundle b).totalSpaceTopology
  exact ⟨E.pathThinNeighborhoods.isCoveringMap_projection b,
    PathThinNeighborhoods.projection_surjective b⟩

/-- The newly constructed cover, rather than an assumed covering input,
lifts each original continuous path with the specified initial total point. -/
theorem path_lift_from_actual_connector (E : LocalEquiconnection X) (b : X)
    (γ : C(I, X)) (e : PathThinNeighborhoods.Total b) (he : γ 0 = e.proj) :
    letI := E.locallyPathConnectedSpace
    letI := (E.pathThinNeighborhoods.prebundle b).totalSpaceTopology
    ∃ Γ : C(I, PathThinNeighborhoods.Total b),
      Bundle.TotalSpace.proj ∘ Γ = γ ∧ Γ 0 = e := by
  let := E.locallyPathConnectedSpace
  let := (E.pathThinNeighborhoods.prebundle b).totalSpaceTopology
  exact (E.pathThinNeighborhoods.isCoveringMap_projection b).exists_path_lifts γ e he

end Quillen.Consumer
