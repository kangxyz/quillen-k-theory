/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionRetractionHomotopy
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the actual completed retraction and its zero component -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableFreeRight
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
namespace Tests.ProjectiveCompletionRetractionHomotopy
variable (R : Type u) [Ring R]

/-- The actual stage-zero inclusion followed by the actual retraction is homotopic to identity. -/
theorem original_stage_zero_square :
    ((classifyingSpaceMapUniversal (completedRetraction R)).comp
      (classifyingSpaceMapUniversal
        (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0))).Homotopic
      (ContinuousMap.id (ClassifyingSpace (StableCompletion.Completion R))) :=
  ⟨completedRetractionStageZeroHomotopy R⟩

/-- The genuine component equivalence has the prescribed original forward map. -/
theorem original_component_forward (x : CompletedTelescopeZeroComponent R) :
    (completedRetractionZeroComponentHomotopyEquiv R x).val =
      classifyingSpaceMapUniversal (completedRetraction R) x.val :=
  completedRetractionZeroComponentHomotopyEquiv_val R x

/-- The total retraction is a weak equivalence even over the zero ring. -/
theorem zero_ring_original_retraction :
    IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (completedRetraction (ZMod 1))) :=
  completedRetraction_isWeakHomotopyEquivalence (ZMod 1)

/-- The zero-ring component inverse remains exactly the original stage-zero inclusion. -/
theorem zero_ring_original_component_inverse (x : StableCompletion.ZeroComponent (ZMod 1)) :
    ((completedRetractionZeroComponentHomotopyEquiv (ZMod 1)).symm x).val =
      classifyingSpaceMapUniversal
        (Grothendieck.ι (projectiveCompletedTelescopeDiagram (ZMod 1)) 0) x.val :=
  completedRetractionZeroComponentHomotopyEquiv_symm_val (ZMod 1) x

end Tests.ProjectiveCompletionRetractionHomotopy
