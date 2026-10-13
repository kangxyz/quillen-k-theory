/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.PathClassSimplyConnected

/-! Independent clients using the actual covering without a supplied-cover premise. -/
@[expose] public section
noncomputable section
universe u
namespace Consumer.PathClassUniversality
open Quillen
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

/-- An actual local connector constructs a same-universe simply connected covering. -/
theorem exists_actual_universal_cover (E : LocalEquiconnection X) (b : X) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (f : C(Y, X)),
      IsCoveringMap f ∧ Function.Surjective f ∧ SimplyConnectedSpace Y := by
  let := E.locallyPathConnectedSpace
  let A := E.pathThinNeighborhoods
  let := (A.prebundle b).totalSpaceTopology
  exact ⟨PathThinNeighborhoods.Total b, inferInstance, A.totalProjection b,
    A.isCoveringMap_projection b, PathThinNeighborhoods.projection_surjective b,
    A.total_simplyConnectedSpace b⟩

/-- Every actual loop upstairs contracts relative to its original basepoint. -/
theorem every_lifted_loop_nullhomotopic [LocallyPathConnectedSpace X]
    (A : PathThinNeighborhoods X) (b : X) :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (e : PathThinNeighborhoods.Total b) (p : Path e e), p.Homotopic (Path.refl e) := by
  let := (A.prebundle b).totalSpaceTopology
  let := A.total_simplyConnectedSpace b
  intro e p
  exact SimplyConnectedSpace.paths_homotopic p (Path.refl e)

end Consumer.PathClassUniversality
