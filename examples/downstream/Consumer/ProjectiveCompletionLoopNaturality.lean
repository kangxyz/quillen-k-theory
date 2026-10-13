/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionZeroLoopNaturality

/-!
# Independent client of the all-points completion-loop homotopy

Evaluation gives an actual continuous path between the two original loops for
every completion-space point, without choosing homotopy-group representatives.
-/

@[expose] public section
noncomputable section

open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
open scoped Topology

universe u

namespace Consumer.ProjectiveCompletionLoopNaturality

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

/-- Each actual completion point has its own continuous naturality track. -/
def comparisonPath {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (Completion R)) :
    Path
      (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f)
        (completionToOriginalQLoops Rᵐᵒᵖ (stageObject R 0) x))
      (completionToOriginalQLoops Sᵐᵒᵖ (stageObject S 0) (completionBaseChangeMap f x)) :=
  (completionToOriginalQLoopsBaseChangeHomotopy f).evalAt x

/-- The resulting two-parameter square keeps the original Q zero vertex on its boundary. -/
theorem comparisonPath_loop_source {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (Completion R)) (t : unitInterval) :
    comparisonPath f x t 0 = classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero :=
  (comparisonPath f x t).source

/-- The other loop boundary is the same specified original Q zero vertex. -/
theorem comparisonPath_loop_target {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (Completion R)) (t : unitInterval) :
    comparisonPath f x t 1 = classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero :=
  (comparisonPath f x t).target

/-- The same track is a genuine path inside the original constant-loop component. -/
def zeroComparisonPath {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ZeroComponent R) :
    Path (zeroOriginalQLoopsBaseChangeMap f (zeroCompletionToOriginalQLoops R x))
      (zeroCompletionToOriginalQLoops S (zeroCompletionBaseChangeMap f x)) :=
  (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f).evalAt x

/-- Component restriction does not replace or reparameterize the original ambient track. -/
theorem zeroComparisonPath_val {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ZeroComponent R) (t : unitInterval) :
    (zeroComparisonPath f x t).val = comparisonPath f x.val t := rfl

end Consumer.ProjectiveCompletionLoopNaturality
