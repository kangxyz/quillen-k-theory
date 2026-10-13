/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.PathClassSimplyConnected

/-! Named tests for actual path-class universality, including a one-point fixture. -/
@[expose] public section
noncomputable section
open Set Bundle
open scoped unitInterval
universe u
namespace QuillenTest.PathClassUniversality

open Quillen
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  [LocallyPathConnectedSpace X] (A : PathThinNeighborhoods X) (b : X)

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] in
/-- Endpoint action starts with the existing based class, in chronological order. -/
theorem endpoint_order {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    (PathThinNeighborhoods.endpointAction b r (.mk p)).toQuotient =
      r.toQuotient.trans (.mk p) := rfl

/-- No chart or subdivision condition occurs in the global endpoint theorem. -/
theorem arbitrary_path_endpoint {e₀ e₁ : PathThinNeighborhoods.Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (γ : Path e₀ e₁),
      e₀.snd.toQuotient.trans (.mk (γ.map (A.totalProjection b).continuous)) =
        e₁.snd.toQuotient := A.path_class_endpoint b

/-- The exact lifted endpoint works for an arbitrary initial fiber class. -/
theorem arbitrary_initial_lift {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    A.pathLift b r p 1 = ⟨y, PathThinNeighborhoods.endpointAction b r (.mk p)⟩ :=
  A.pathLift_endpoint b r p

/-- The endpoint class retains the actual dependent projection transport. -/
theorem endpoint_transport_visible {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    (A.pathLift b r p 1).snd.toQuotient =
      (r.toQuotient.trans (.mk p)).cast rfl
        ((A.pathLift_proj b r p 1).trans p.target) :=
  A.pathLift_endpoint_class b r p

/-- Every literal point is joined to the neutral class, without chart normalization. -/
theorem all_points_reachable (e : PathThinNeighborhoods.Total b) :
    letI := (A.prebundle b).totalSpaceTopology
    Joined (PathThinNeighborhoods.totalBasepoint b) e := A.joined_totalBasepoint b e

/-- The constructed covering is connected through actual continuous paths. -/
theorem actual_total_path_connected :
    letI := (A.prebundle b).totalSpaceTopology
    PathConnectedSpace (PathThinNeighborhoods.Total b) := A.total_pathConnectedSpace b

/-- Arbitrary fixed-endpoint paths have a unique actual upstairs homotopy class. -/
theorem upstairs_classes_unique (e₀ e₁ : PathThinNeighborhoods.Total b) :
    letI := (A.prebundle b).totalSpaceTopology
    Subsingleton (Path.Homotopic.Quotient e₀ e₁) := A.total_pathClass_subsingleton b e₀ e₁

/-- Simple connectedness is a conclusion of the construction. -/
theorem actual_total_simply_connected :
    letI := (A.prebundle b).totalSpaceTopology
    SimplyConnectedSpace (PathThinNeighborhoods.Total b) := A.total_simplyConnectedSpace b

/-- A one-point geometric input contains no assumed total-space conclusion. -/
def onePointNeighborhoods : PathThinNeighborhoods PUnit where
  neighborhood _ := univ
  isOpen_neighborhood _ := isOpen_univ
  mem_neighborhood _ := mem_univ _
  isPathConnected_neighborhood _ := isPathConnected_univ
  ambientPathThin _ := by
    intro x y p q _ _
    exact SimplyConnectedSpace.paths_homotopic p q

/-- The one-point fixture exercises the constructed simply connected covering. -/
theorem one_point_total_simply_connected :
    letI := (onePointNeighborhoods.prebundle PUnit.unit).totalSpaceTopology
    SimplyConnectedSpace (PathThinNeighborhoods.Total PUnit.unit) :=
  onePointNeighborhoods.total_simplyConnectedSpace PUnit.unit

end QuillenTest.PathClassUniversality
