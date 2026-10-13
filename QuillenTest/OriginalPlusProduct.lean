/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveOriginalPlusProductNaturality

/-!
# Exact original plus-product normalization tests

The plus factor and its standard Q map are unchanged. Test the entire neutral
slice, its prescribed basepoint path, original first-coordinate classifier,
and positive numerator-minus-denominator stage label.
-/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open scoped Topology
universe u
namespace QuillenTest.OriginalPlusProduct

variable (R : Type u) [Ring R]

/-- Every original plus-model point is sent by exactly its standard zero-component comparison. -/
theorem entire_neutral_slice (z : StableCompletion.ZeroComponent R) :
    originalPlusProductToQLoopsHomotopyEquiv R
      ((exactStructure Rᵐᵒᵖ).discreteKZeroIdentity, z) =
        (StableCompletion.zeroCompletionToOriginalQLoops R z).val :=
  originalPlusProductToQLoopsHomotopyEquiv_neutral R z

/-- Neutral normalization preserves the entire specified original comparison track. -/
theorem original_basepoint_track (t : unitInterval) :
    originalPlusProductBasepointPath R t =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (StableCompletion.stageObject R 0) t :=
  originalPlusProductBasepointPath_apply R t

/-- The full product retains exactly the original K₀ classifier of every original Q loop. -/
theorem original_classifier
    (γ : Path (exactStructure.{u, u} Rᵐᵒᵖ).kBasepoint (exactStructure Rᵐᵒᵖ).kBasepoint) :
    ((originalQLoopsPlusProductHomotopyEquiv R γ).1).ofTopology =
      (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv (ZerothHomotopy.mk γ) := by
  rw [originalQLoopsPlusProductHomotopyEquiv_label]
  rfl

/-- The standard original stage label is numerator-minus-denominator, without inversion. -/
theorem positive_stage (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    ((originalQLoopsPlusProductHomotopyEquiv R
      (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P)))).1).ofTopology =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of :=
  originalQLoopsPlusProductHomotopyEquiv_stage_label R n P

end QuillenTest.OriginalPlusProduct
