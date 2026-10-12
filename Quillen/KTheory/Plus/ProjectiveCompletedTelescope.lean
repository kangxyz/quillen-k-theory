/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveTelescopeInterchange
public import Quillen.Topology.ClassifyingSpace.LocalizationTelescope
public import Quillen.Topology.ClassifyingSpace.LocalizationTelescopeHomotopyEquiv
public import Quillen.Topology.LocalCoefficients.HomotopyEquivalence

/-!
# Original completed projective stage homotopy equivalences

Each original completed-stage map into localization of the right-projective
telescope admits a genuine homotopy inverse. Its original forward map therefore
induces isomorphisms for every target local system and every homology degree.
The construction assumes only a unital ring; it does not assert acyclicity
of the distinct completion map from the precompletion telescope.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u
namespace Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  projectiveTelescopeAction
variable (R : Type u) [Ring R]

/-- The original completed category maps by a weak equivalence into localization
of the original right-projective telescope, at every specified stage. -/
theorem projectiveCompletionStage_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (projectiveCompletionStage R n)) :=
  TranslationTelescope.localizationStage_isWeakHomotopyEquivalence (freeIso Rᵐᵒᵖ 1) n

/-- The original completed telescope stage inclusion is a weak equivalence. -/
theorem projectiveCompletedStageInclusion_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal
      (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) n)) :=
  TranslationTelescope.completedStageInclusion_isWeakHomotopyEquivalence (freeIso Rᵐᵒᵖ 1) n

/-- The specified completed-stage map itself admits a genuine homotopy inverse. -/
def projectiveCompletionStageHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (StableCompletion.Completion R))
      (ClassifyingSpace (ProjectiveTelescopeLocalization R)) :=
  TranslationTelescope.localizationStageHomotopyEquiv.{u + 1, u} (freeIso Rᵐᵒᵖ 1) n

/-- The homotopy equivalence retains the original forward stage map. -/
theorem projectiveCompletionStageHomotopyEquiv_toFun (n : ℕ) :
    (projectiveCompletionStageHomotopyEquiv R n).toFun =
      classifyingSpaceMapUniversal (projectiveCompletionStage R n) :=
  TranslationTelescope.localizationStageHomotopyEquiv_toFun.{u + 1, u} _ n

/-- Every target local system, without an abelian-monodromy restriction, is
preserved by the original completed-stage map. -/
theorem projectiveCompletionStage_localHomology_isIso (n : ℕ)
    (A : LocalCoefficients.System.{u + 1, u + 1}
      (ClassifyingSpace (ProjectiveTelescopeLocalization R))) (d : ℕ) :
    IsIso (LocalCoefficients.pushforwardHomologyMap
      (classifyingSpaceMapUniversal (projectiveCompletionStage R n)) A d) := by
  rw [← projectiveCompletionStageHomotopyEquiv_toFun]
  exact LocalCoefficients.isIso_pushforwardHomologyMap_of_homotopyEquiv _ A d

end Quillen.FiniteProjectiveModule
