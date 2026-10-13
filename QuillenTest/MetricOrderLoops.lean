/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.LoopEquiconnection
public import QuillenTest.MetricOrderCommonPoint
import Mathlib.Tactic.NormNum

/-!
# Actual compact-open loops along incomparable support branches

Travel from the shared vertex to each of the two incomparable branch points
and back. The resulting original Path loops stay in the common vertex star,
so they belong to the pointwise loop connector domain. The compatible sup
metric, original topology, and all endpoint/diagonal identities are checked
on these literal paths.
-/

@[expose] public section
noncomputable section

open Quillen Quillen.MetricOrderComplex QuillenTest.MetricOrderCommonPoint
open scoped Topology unitInterval

namespace QuillenTest.MetricOrderLoops

/-- The actual outward path to one of the incomparable support branches. -/
def outward (b : Bool) : Path (vertex (∅ : Set Bool)) (branchPoint b) :=
  connectorPath _ _ (commonMass_pos_of_mem_vertexStar (v := (∅ : Set Bool))
    (by norm_num [vertexStar]) (by norm_num [vertexStar, branchPoint_weights]))

/-- The literal out-and-back loop based at the shared original vertex. -/
def branchLoop (b : Bool) : Path (vertex (∅ : Set Bool)) (vertex (∅ : Set Bool)) :=
  (outward b).trans (outward b).symm

/-- Every point of the outward path retains the common star. -/
theorem outward_mem_star (b : Bool) (t : I) : outward b t ∈ vertexStar (∅ : Set Bool) := by
  apply connectorPath_coordinate_pos
  · norm_num
  · norm_num [branchPoint_weights]

/-- Both halves of the actual loop stay inside that common star. -/
theorem branchLoop_mem_star (b : Bool) (t : I) :
    branchLoop b t ∈ vertexStar (∅ : Set Bool) := by
  have hr := Set.mem_range_self (f := branchLoop b) t
  rw [branchLoop, Path.trans_range, Path.symm_range, Set.union_self] at hr
  obtain ⟨s, hs⟩ := hr
  change outward b s = branchLoop b t at hs
  rw [← hs]
  exact outward_mem_star b s

/-- The two different support-branch loops lie in the actual pointwise connector domain. -/
theorem branchLoops_domain :
    (branchLoop false, branchLoop true) ∈ (loopEquiconnection (∅ : Set Bool)).domain :=
  fun t ↦ commonMass_pos_of_mem_vertexStar
    (branchLoop_mem_star false t) (branchLoop_mem_star true t)

/-- Pointwise shared support yields strict distance <2 in the original compatible sup metric. -/
theorem branchLoops_dist_lt_two : dist (branchLoop false) (branchLoop true) < 2 :=
  (loop_domain_iff_dist_lt_two _ _ _).mp branchLoops_domain

/-- The loop connector has its exact initial loop. -/
theorem branchLoops_connector_zero :
    (loopEquiconnection (∅ : Set Bool)).connector
      (⟨(branchLoop false, branchLoop true), branchLoops_domain⟩, 0) = branchLoop false :=
  (loopEquiconnection (∅ : Set Bool)).connector_zero _

/-- The loop connector has its exact terminal loop. -/
theorem branchLoops_connector_one :
    (loopEquiconnection (∅ : Set Bool)).connector
      (⟨(branchLoop false, branchLoop true), branchLoops_domain⟩, 1) = branchLoop true :=
  (loopEquiconnection (∅ : Set Bool)).connector_one _

/-- Every whole out-and-back loop is retained at every time on the diagonal. -/
theorem branchLoop_diagonal (b : Bool) (t : I) :
    (loopEquiconnection (∅ : Set Bool)).connector
      (⟨(branchLoop b, branchLoop b), (loopEquiconnection _).diagonal_mem _⟩, t) = branchLoop b :=
  (loopEquiconnection (∅ : Set Bool)).connector_diagonal _ t

/-- The metric construction retains the original Path topology definitionally. -/
theorem originalPathTopology :
    (PathSpace.instMetricSpace (x := vertex (∅ : Set Bool)) (y := vertex ∅)
      |>.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) = Path.instTopologicalSpace :=
  PathSpace.metricSpace_topology

/-- Each nontrivial branch loop has a genuine open connector-convex neighborhood. -/
theorem branchLoop_convex_open_neighborhood (b : Bool) :
    ∃ W : Set (Path (vertex (∅ : Set Bool)) (vertex ∅)),
      IsOpen W ∧ branchLoop b ∈ W ∧ (loopEquiconnection ∅).IsConvex W :=
  exists_convex_open_loop_neighborhood ∅ (branchLoop b)

end QuillenTest.MetricOrderLoops
