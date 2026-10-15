/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.GrothendieckTelescopeHomotopyEquiv
public import Quillen.Topology.ClassifyingSpace.EndofunctorIterationHomotopy
public import Quillen.Topology.ClassifyingSpace.GroupCompletionTranslation
public import Quillen.CategoryTheory.GroupCompletion.TelescopeInterchangeEquivalence

/-! # Genuine homotopy equivalences for the original completed stage maps -/

@[expose] public section

open Quillen.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
open GroupCompletion
variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- Every transition of the original completed diagram has its actual iterated
homotopy inverse, retaining the given forward map. -/
theorem completedTransitionHomotopyEquiv_toFun {n m : ℕ} (h : n ⟶ m) :
    (EndofunctorTelescope.iterateClassifyingHomotopyEquiv
      (Localization.translationClassifyingHomotopyEquiv e).symm (m - n)).toFun =
        (classifyingSpaceMap ((localizationDiagram e).map h).toFunctor).hom := by
  change _ = (classifyingSpaceMap (localizationIteration e (m - n))).hom
  rw [localizationIteration_eq]
  have hh := EndofunctorTelescope.iterateClassifyingHomotopyEquiv_toFun
    (Localization.secondTranslation e) (Localization.translationClassifyingHomotopyEquiv e).symm
    (by rw [classifyingSpaceMapUniversal_eq]; rfl) (m - n)
  rw [classifyingSpaceMapUniversal_eq] at hh
  exact hh

/-- The original completed-stage inclusion is the forward map of a genuine
homotopy equivalence, obtained from finite prefixes and compact HELP. -/
def completedStageInclusionHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C C))
      (ClassifyingSpace (Grothendieck (localizationDiagram e))) :=
  GrothendieckTelescope.fiberInclusionHomotopyEquiv (localizationDiagram e)
    (fun {i j} _ ↦ EndofunctorTelescope.iterateClassifyingHomotopyEquiv
      (Localization.translationClassifyingHomotopyEquiv e).symm (j - i))
    (fun _ ↦ completedTransitionHomotopyEquiv_toFun e _) n

/-- The chosen equivalence retains exactly the original stage inclusion. -/
theorem completedStageInclusionHomotopyEquiv_toFun (n : ℕ) :
    (completedStageInclusionHomotopyEquiv e n).toFun =
      classifyingSpaceMapUniversal (Grothendieck.ι (localizationDiagram e) n) := by
  rw [classifyingSpaceMapUniversal_eq]
  exact GrothendieckTelescope.fiberInclusionHomotopyEquiv_toFun _ _ _ n

/-- The original map from the completed category to localization of the original
telescope has a genuine homotopy inverse. -/
def localizationStageHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C C))
      (ClassifyingSpace (Localization C (Model e))) :=
  (completedStageInclusionHomotopyEquiv e n).trans
    (equivalenceClassifyingHomotopyEquivUniversal (localizationInterchangeEquivalence e))

/-- The genuine homotopy equivalence uses the original completed-stage map. -/
theorem localizationStageHomotopyEquiv_toFun (n : ℕ) :
    (localizationStageHomotopyEquiv e n).toFun =
      classifyingSpaceMapUniversal (localizationStage e n) := by
  change (classifyingSpaceMapUniversal (localizationInterchange e)).comp
    (completedStageInclusionHomotopyEquiv e n).toFun = _
  rw [completedStageInclusionHomotopyEquiv_toFun]
  erw [← classifyingSpaceMapUniversal_comp, localizationInterchange_stage]
  rfl

end Quillen.TranslationTelescope
