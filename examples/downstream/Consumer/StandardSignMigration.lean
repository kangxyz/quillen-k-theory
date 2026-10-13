/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus
public import Quillen.KTheory.Plus.ProjectiveCompletionLoopLabels

/-! # Standard comparison component and stage labels -/

@[expose] public section
noncomputable section
open scoped Topology
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
universe u
namespace Consumer.StandardSignMigration
variable {R S : Type u} [Ring R] [Ring S]

/-- An arbitrary displayed basepoint contributes exactly its original class. -/
theorem translated_component_label (U : GroupCompletionCategory R)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R))) :
    (exactStructure R).loopComponentsKZeroEquiv
        (completionToOriginalQLoopsComponents R U a) * completionKZeroClass R U =
      completionZerothHomotopyKZeroEquiv R a := by
  rw [completionToOriginalQLoopsComponents_kZero, div_mul_cancel]

/-- The actual additive-zero-pair comparison classifies components with no sign adjustment. -/
theorem canonical_labels_detect_components
    (x y : ClassifyingSpace (GroupCompletionCategory R)) :
    (exactStructure R).loopComponentsKZeroEquiv
        (ZerothHomotopy.mk (originalQComparison R x)) =
      (exactStructure R).loopComponentsKZeroEquiv
        (ZerothHomotopy.mk (originalQComparison R y)) ↔ Joined x y := by
  rw [originalQComparison_kZero, originalQComparison_kZero,
    (completionZerothHomotopyKZeroEquiv R).injective.eq_iff]
  exact Quotient.eq

/-- The actual positive stage has the standard numerator and denominator. -/
theorem positive_stage_label (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P)))) =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of :=
  completionToOriginalQLoops_stage_kZero R n P

end Consumer.StandardSignMigration
