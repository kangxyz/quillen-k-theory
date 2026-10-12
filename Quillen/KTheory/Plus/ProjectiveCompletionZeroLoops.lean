/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Topology.ClassifyingSpace.ProjectiveCompletionLoops
public import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionBased
public import Quillen.Topology.HomotopyGroups.PathComponentWeakEquivalence

/-! # The original zero completion and the identity component of original Q loops -/
@[expose] public section
noncomputable section
universe u
namespace Quillen.FiniteProjectiveModule.StableCompletion
variable (R : Type u) [Ring R]

/-- The identity component in the unchanged original loop space of Q. -/
abbrev OriginalQLoopsZeroComponent :=
  pathComponent (Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))

/-- The original completion-to-loop map restricted to its actual zero component. -/
def zeroCompletionToOriginalQLoops : C(ZeroComponent R, OriginalQLoopsZeroComponent R) :=
  pathComponentMap (completionToOriginalQLoops Rᵐᵒᵖ (stageObject R 0))
    (zeroPoint R) (Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))
    ⟨completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0)⟩

/-- The underlying map is precisely the parameterized original Q comparison. -/
@[simp] theorem zeroCompletionToOriginalQLoops_val (x : ZeroComponent R) :
    (zeroCompletionToOriginalQLoops R x).val =
      completionToOriginalQLoops Rᵐᵒᵖ (stageObject R 0) x.val := rfl

/-- The actual component comparison is a weak equivalence, including degree zero. -/
theorem zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (zeroCompletionToOriginalQLoops R) :=
  (completionToOriginalQLoops_isWeakHomotopyEquivalence Rᵐᵒᵖ (stageObject R 0)).pathComponentMap
    (zeroPoint R) _ ⟨completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0)⟩

/-- The basepoint track is the restriction of the specified original comparison track. -/
def zeroCompletionToOriginalQLoopsBasepointPath :
    Path (zeroCompletionToOriginalQLoops R (zeroBase R))
      ⟨Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero),
        mem_pathComponent_self _⟩ :=
  pathComponentMapBasepointPath _ (zeroPoint R) _
    (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0))

/-- Every point of the restricted track is the original track, without reparametrization. -/
@[simp] theorem zeroCompletionToOriginalQLoopsBasepointPath_val (t : unitInterval) :
    (zeroCompletionToOriginalQLoopsBasepointPath R t).val =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0) t := rfl

end Quillen.FiniteProjectiveModule.StableCompletion
