/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.Equiconnection
public import QuillenTest.MetricOrderCommonPoint
import Mathlib.Tactic.NormNum

/-!
# The connector on a genuine non-simplex pair

The two branch points have a non-chain support union. The actual connector
still exists, goes through the shared vertex at its midpoint, stays in the
shared open star, and retains every point of the whole diagonal.
All checks are named declarations for the origin-scoped audit.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Quillen Quillen.MetricOrderComplex QuillenTest.MetricOrderCommonPoint
open scoped Topology unitInterval

namespace QuillenTest.MetricOrderEquiconnection

/-- The incomparable branch pair lies in the actual open connector domain. -/
def forkPair : OverlappingPairs (Set Bool) :=
  ⟨(branchPoint false, branchPoint true), by rw [fork_commonMass]; norm_num⟩

/-- The actual connector starts at the first branch point. -/
theorem fork_source : connector (forkPair, 0) = branchPoint false := connector_zero forkPair

/-- The actual connector ends at the second branch point. -/
theorem fork_target : connector (forkPair, 1) = branchPoint true := connector_one forkPair

/-- The connector midpoint is exactly the common original vertex. -/
theorem fork_midpoint :
    connector (forkPair, ⟨1 / 2, by constructor <;> norm_num⟩) = vertex (∅ : Set Bool) := by
  change connectorPath (branchPoint false) (branchPoint true) _ _ = _
  rw [connectorPath, Path.trans_apply]
  norm_num
  convert fork_commonPoint using 1

/-- Both branches retain the common vertex throughout the whole connector. -/
theorem fork_stays_in_common_star (t : I) :
    connector (forkPair, t) ∈ vertexStar (∅ : Set Bool) := by
  apply connectorPath_coordinate_pos
  · norm_num [forkPair, branchPoint_weights]
  · norm_num [forkPair, branchPoint_weights]

/-- Even a nonvertex distribution is fixed on the whole diagonal. -/
theorem branch_diagonal_fixed (b : Bool) (t : I) :
    connector (⟨(branchPoint b, branchPoint b), by simp⟩, t) = branchPoint b :=
  connector_diagonal (branchPoint b) t

/-- The common star is a genuine open connector-convex neighborhood of the sample. -/
theorem common_star_open : IsOpen (vertexStar (∅ : Set Bool)) := isOpen_vertexStar _

/-- There is no hidden chain-union hypothesis in the verified non-simplex sample. -/
theorem fork_union_not_chain :
    ¬IsChain (· ≤ ·) (((branchPoint false).weights.support ∪
      (branchPoint true).weights.support : Finset (Set Bool)) : Set (Set Bool)) :=
  fork_support_union_not_chain

end QuillenTest.MetricOrderEquiconnection
