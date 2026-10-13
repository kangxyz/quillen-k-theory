/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.ProjectiveCompletionHomotopyFiber
public import Quillen.Topology.HomotopyFiber.ContractibleSourcePath

/-! # The original projective completion and loops in the original Q space

The chosen fiber point and its entire path are retained. The comparison has
weak-equivalence strength; no Whitehead upgrade or plus assertion is used.
-/
@[expose] public section
noncomputable section
open scoped Topology ZeroObject
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.FiniteProjectiveModule
variable (R : Type u) [Ring R]

/-- The actual image of a specified completion vertex in the original homotopy fiber. -/
def completionQFiberPoint (U : GroupCompletionCategory R) :
    HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint (exactStructure R).qZero) :=
  completionToOriginalQHomotopyFiber R (classifyingSpacePoint U)

/-- Contractibility of the actual localized total space gives an explicit loop/fiber
homotopy equivalence, corrected by the original vertex path. -/
def originalQLoopFiberHomotopyEquiv (U : GroupCompletionCategory R) :
    ContinuousMap.HomotopyEquiv
      (Path (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpacePoint (exactStructure R).qZero))
      (HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection R))
        (classifyingSpacePoint (exactStructure R).qZero)) := by
  let : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
    localizedExtension_classifyingSpace_contractible R
  exact HomotopyFiber.loopEquivOfContractibleSourcePath _ (completionQFiberPoint R U).1.1 _
    (HomotopyFiber.toPath _ _ (completionQFiberPoint R U))

/-- The completion maps to loops in the unchanged original Q space. -/
def completionToOriginalQLoops (U : GroupCompletionCategory R) :
    C(ClassifyingSpace (GroupCompletionCategory R),
      Path (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpacePoint (exactStructure R).qZero)) :=
  (originalQLoopFiberHomotopyEquiv R U).invFun.comp
    (completionToOriginalQHomotopyFiber R)

/-- The chosen vertex is sent to the constant loop along a specified original track. -/
def completionToOriginalQLoopsBasepointPath (U : GroupCompletionCategory R) :
    Path (completionToOriginalQLoops R U (classifyingSpacePoint U))
      (Path.refl (classifyingSpacePoint (exactStructure R).qZero)) := by
  let : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
    localizedExtension_classifyingSpace_contractible R
  exact HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
    (completionQFiberPoint R U).1.1 _ (HomotopyFiber.toPath _ _ (completionQFiberPoint R U))

/-- The actual loop comparison is a weak equivalence on all components. -/
theorem completionToOriginalQLoops_isWeakHomotopyEquivalence (U : GroupCompletionCategory R) :
    IsWeakHomotopyEquivalence (completionToOriginalQLoops R U) :=
  (isWeakHomotopyEquivalence_of_homotopyEquiv
    (originalQLoopFiberHomotopyEquiv R U).symm).comp
      (completionToOriginalQHomotopyFiber_isWeakHomotopyEquivalence R)

/-- The original additive zero pair fixes the canonical based comparison. -/
def completionZeroPair : GroupCompletionCategory R :=
  completionPair R ⟨0⟩ ⟨0⟩

/-- The canonical zero-based comparison with loops in the original Q construction. -/
def originalQComparison :
    C(ClassifyingSpace (GroupCompletionCategory R),
      Path (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpacePoint (exactStructure R).qZero)) :=
  completionToOriginalQLoops R (completionZeroPair R)

/-- The canonical comparison is a weak equivalence, including dimension zero. -/
theorem originalQComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (originalQComparison R) :=
  completionToOriginalQLoops_isWeakHomotopyEquivalence R (completionZeroPair R)

/-- The canonical comparison carries its specified original zero track. -/
def originalQComparisonBasepointPath :
    Path (originalQComparison R (classifyingSpacePoint (completionZeroPair R)))
      (Path.refl (classifyingSpacePoint (exactStructure R).qZero)) :=
  completionToOriginalQLoopsBasepointPath R (completionZeroPair R)

end Quillen.FiniteProjectiveModule
