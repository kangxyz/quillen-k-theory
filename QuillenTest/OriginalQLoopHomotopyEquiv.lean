/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionLoopHomotopyEquiv
public import Quillen.KTheory.Plus.ProjectiveCompletionLoopKZero

/-!
# Exact standard original Q-comparison upgrade tests

Test the constructed domination endpoints for independent category universes,
the exact standard forward map and positive label, and the original restricted
basepoint track of the plus-certified zero-component comparison.
-/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open scoped Topology
universe u v
namespace QuillenTest.OriginalQLoopHomotopyEquiv

/-- The actual transported domination starts at the constructed composite on original loops. -/
theorem domination_zero {C : Type u} [Category.{v} C] (c : C)
    (γ : Path (classifyingSpacePoint c) (classifyingSpacePoint c)) :
    (RankedChainOrder.universalLoopDominationData C c).2.2.2 (0, γ) =
      (RankedChainOrder.universalLoopDominationData C c).2.2.1
        ((RankedChainOrder.universalLoopDominationData C c).2.1 γ) :=
  (RankedChainOrder.universalLoopDominationData C c).2.2.2.apply_zero γ

/-- The actual transported domination ends at the identity on original loops. -/
theorem domination_one {C : Type u} [Category.{v} C] (c : C)
    (γ : Path (classifyingSpacePoint c) (classifyingSpacePoint c)) :
    (RankedChainOrder.universalLoopDominationData C c).2.2.2 (1, γ) = γ :=
  (RankedChainOrder.universalLoopDominationData C c).2.2.2.apply_one γ

variable (R : Type u) [Ring R]

/-- The canonical upgraded forward map is precisely the accepted standard map. -/
theorem original_forward :
    (originalQComparisonHomotopyEquiv R).toFun = originalQComparison R :=
  originalQComparisonHomotopyEquiv_toFun R

/-- The upgraded forward map retains its positive original K₀ label. -/
theorem original_positive_label (x : ClassifyingSpace (GroupCompletionCategory R)) :
    (exactStructure R).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (originalQComparisonHomotopyEquiv R x)) =
        completionZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk x) :=
  originalQComparison_kZero R x

/-- Every point of the original zero-component basepoint track is unchanged. -/
theorem original_zero_track (t : unitInterval) :
    (StableCompletion.zeroCompletionHomotopyEquivBasepointPath R t).val =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (StableCompletion.stageObject R 0) t :=
  StableCompletion.zeroCompletionHomotopyEquivBasepointPath_val R t

end QuillenTest.OriginalQLoopHomotopyEquiv
