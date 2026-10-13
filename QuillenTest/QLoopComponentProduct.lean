/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveQLoopComponentProduct
public import QuillenTest.MetricOrderLoops

/-!
# Original loop components and normalized positive-label product tests

Check open components for the literal incomparable-support branch loops, then
check exact neutral normalization, original classifier recovery, and the
accepted positive standard-comparison label on the actual original Q target.
-/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule Quillen.MetricOrderComplex
open scoped Topology
universe u
namespace QuillenTest.QLoopComponentProduct

/-- The actual non-chain-branch loop has an open component in the unchanged Path topology. -/
theorem branchLoop_open_component (b : Bool) :
    IsOpen (pathComponent (QuillenTest.MetricOrderLoops.branchLoop b)) :=
  (loopEquiconnection (∅ : Set Bool)).isOpen_pathComponent _

variable (R : Type u) [Ring R]

/-- The chosen neutral representative is the exact original constant Q loop. -/
theorem original_neutral_representative :
    (exactStructure.{u, u} R).qLoopRepresentative (exactStructure R).discreteKZeroIdentity =
      Path.refl (exactStructure R).kBasepoint :=
  (exactStructure R).qLoopRepresentative_identity

/-- The inverse product map is the exact inclusion on the entire original neutral component. -/
theorem original_neutral_slice (z : (exactStructure.{u, u} R).QLoopIdentityComponent) :
    (originalQLoopProductEquiv R).invFun ((exactStructure R).discreteKZeroIdentity, z) = z.val :=
  originalQLoopProductEquiv_neutral_slice R z

/-- Every original loop retains its exact K₀ value under the product decomposition. -/
theorem original_loop_label (γ : Path (exactStructure.{u, u} R).kBasepoint
    (exactStructure R).kBasepoint) :
    ((originalQLoopProductEquiv R γ).1).ofTopology =
      (exactStructure R).loopComponentsKZeroEquiv (ZerothHomotopy.mk γ) := by
  rw [originalQLoopProductEquiv, ExactStructure.qLoopProductEquiv_label]
  rfl

/-- The standard original comparison has positive, unchanged completion class. -/
theorem original_comparison_positive (x : ClassifyingSpace (GroupCompletionCategory R)) :
    ((originalQLoopProductEquiv R (originalQComparison R x)).1).ofTopology =
      completionZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk x) :=
  originalQLoopProductEquiv_comparison_label R x

end QuillenTest.QLoopComponentProduct
