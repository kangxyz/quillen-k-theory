/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionLoopLabels

/-!
# An independent consumer of the standard loop comparison's K₀ labels

Every original K₀ class is attained by the original completion-loop comparison
at an actual finite telescope stage. Equality of the loop labels detects the
original completion components. Both facts use the proved sign explicitly.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
universe u
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
namespace Consumer.OriginalCompletionLoopLabels
variable {R : Type u} [Ring R]

/-- Every unchanged K₀ class is represented by the exact original loop map at a finite stage. -/
theorem exists_original_stage_loop (k : (exactStructure Rᵐᵒᵖ).K 0) :
    ∃ (n : ℕ) (P : IsoCategory Rᵐᵒᵖ),
      (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
        (ZerothHomotopy.mk (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
          (classifyingSpaceMapUniversal (StableFreeRight.completionFunctor R)
            (classifyingSpacePoint
              (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R))))) = k := by
  obtain ⟨a, ha⟩ := (StableFreeRight.telescopeZerothHomotopyKZeroEquiv R).surjective k
  obtain ⟨⟨n, ⟨P⟩⟩, rfl⟩ :=
    classifyingSpaceVertexComponent_surjective (ProjectiveTelescope R) a
  refine ⟨n, P, ?_⟩
  rw [telescopeToOriginalQLoops_stage_kZero]
  exact (StableFreeRight.telescopeZerothHomotopyKZeroEquiv_stage R n P).symm.trans ha

/-- The original Q-loop labels classify the original completion points' path components. -/
theorem original_loop_labels_detect_components
    (x y : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk
        (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0) x)) =
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk
        (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0) y)) ↔ Joined x y := by
  rw [← completionToOriginalQLoopsComponents_mk, ← completionToOriginalQLoopsComponents_mk,
    completionToOriginalQLoopsComponents_zeroStage, completionToOriginalQLoopsComponents_zeroStage,
    (completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ).injective.eq_iff]
  exact Quotient.eq

end Consumer.OriginalCompletionLoopLabels
