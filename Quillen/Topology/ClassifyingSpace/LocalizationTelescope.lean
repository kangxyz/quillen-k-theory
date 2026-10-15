/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.TelescopeWeakBase
public import Quillen.Topology.ClassifyingSpace.GroupCompletionTranslation
public import Quillen.CategoryTheory.GroupCompletion.TelescopeInterchangeEquivalence

/-! # Actual completed stages in localization of the original telescope -/

@[expose] public section

open Quillen.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
open GroupCompletion
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- Every actual completed-stage inclusion into its original telescope is a weak equivalence. -/
theorem completedStageInclusion_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (Grothendieck.ι (localizationDiagram e) n)) := by
  rw [localizationDiagram_eq]
  apply EndofunctorTelescope.stageInclusion_isWeakHomotopyEquivalence _
    (Localization.translationClassifyingHomotopyEquiv e).symm
  rw [classifyingSpaceMapUniversal_eq]
  rfl

/-- The original completed-stage map into localization of the precompletion telescope
is a weak equivalence. Its unit square is `localizationStage_unitEntry`. -/
theorem localizationStage_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (localizationStage e n)) := by
  have hi := completedStageInclusion_isWeakHomotopyEquivalence e n
  have he := isWeakHomotopyEquivalence_of_homotopyEquiv
    (equivalenceClassifyingHomotopyEquivUniversal (localizationInterchangeEquivalence e))
  change IsWeakHomotopyEquivalence
    (classifyingSpaceMapUniversal (localizationInterchange e)) at he
  have h := he.comp hi
  rw [← classifyingSpaceMapUniversal_comp, localizationInterchange_stage] at h
  exact h

end Quillen.TranslationTelescope
