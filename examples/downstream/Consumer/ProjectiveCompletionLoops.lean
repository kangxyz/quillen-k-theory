/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.ProjectiveCompletionLoops

/-! # Direct standard completion-loop comparison and its specified track -/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
universe u
namespace Consumer.ProjectiveCompletionLoops
variable (R : Type u) [Ring R]

/-- The original fiber path is unchanged despite standardizing the public comparison. -/
theorem original_fiber_path (U : GroupCompletionCategory R) (t : unitInterval) :
    (completionToOriginalQHomotopyFiber R (classifyingSpacePoint U)).1.2 t =
      classifyingSpacePath ((completionIdentityProjectionIsoZero R).inv.app U)
        (unitInterval.symm t) :=
  completionToOriginalQHomotopyFiber_vertex_path R U t

/-- The actual zero-based standard map has full weak-equivalence strength. -/
theorem standard_zero_weak : IsWeakHomotopyEquivalence (originalQComparison R) :=
  originalQComparison_isWeakHomotopyEquivalence R

-- The standard map is the generic fiber inverse followed by one reversal.
example (R : Type u) [Ring R] (U : GroupCompletionCategory R) :
    completionToOriginalQLoops R U =
      loopReversal.comp ((originalQLoopFiberHomotopyEquiv R U).invFun.comp
        (completionToOriginalQHomotopyFiber R)) :=
  completionToOriginalQLoops_eq_reversal_fiberInverse R U

-- The supplied track is the specified reversed generic inverse track.
example
    (U : GroupCompletionCategory R) :
    letI : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
      localizedExtension_classifyingSpace_contractible R
    completionToOriginalQLoopsBasepointPath R U =
      loopReversalPath
        (HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
          (completionQFiberPoint R U).1.1 _
          (HomotopyFiber.toPath _ _ (completionQFiberPoint R U))) := rfl

end Consumer.ProjectiveCompletionLoops
