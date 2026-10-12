/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionRetraction
public import Quillen.Topology.ClassifyingSpace.UniverseHomotopy
public import Quillen.Topology.HomotopyEquiv.HomotopySquare
public import Quillen.Topology.HomotopyEquiv.PathComponent

/-!
# The original completed retraction is a homotopy equivalence

The actual completed stage-zero inclusion is a homotopy equivalence. Its
composite with the prescribed inverse cocone is identified with the identity
by the original unitor natural isomorphism. The resulting homotopy square
therefore makes the original retraction itself a homotopy equivalence.
Restricting along the actual unitor path preserves its genuine zero component
and retains exactly the original forward map.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u
namespace Quillen.FiniteProjectiveModule.StableFreeRight
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- The prescribed completed base is the original zero pair in stage zero. -/
def completedTelescopeBase : Grothendieck (projectiveCompletedTelescopeDiagram R) :=
  (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0).obj
    (StableCompletion.stageObject R 0)

/-- The original completed stage-zero inclusion has a genuine homotopy inverse. -/
def completedStageZeroHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (StableCompletion.Completion R))
      (ClassifyingSpace (Grothendieck (projectiveCompletedTelescopeDiagram R))) :=
  TranslationTelescope.completedStageInclusionHomotopyEquiv.{u + 1, u}
    (freeIso Rᵐᵒᵖ 1) 0

/-- The stage-zero equivalence retains the original inclusion as its forward map. -/
lemma completedStageZeroHomotopyEquiv_toFun :
    (completedStageZeroHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0) :=
  TranslationTelescope.completedStageInclusionHomotopyEquiv_toFun.{u + 1, u}
    (freeIso Rᵐᵒᵖ 1) 0

/-- The specified natural unitor realizes the original retraction-inclusion homotopy. -/
def completedRetractionStageZeroHomotopy :
    ((classifyingSpaceMapUniversal (completedRetraction R)).comp
      (classifyingSpaceMapUniversal
        (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0))).Homotopy
      (ContinuousMap.id (ClassifyingSpace (StableCompletion.Completion R))) :=
  (classifyingSpaceUniversalHomotopy (completedRetractionZeroIso R).hom).cast
    (classifyingSpaceMapUniversal_comp _ _) classifyingSpaceMapUniversal_id

/-- The actual completed retraction is the forward map of a genuine homotopy equivalence. -/
def completedRetractionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (Grothendieck (projectiveCompletedTelescopeDiagram R)))
      (ClassifyingSpace (StableCompletion.Completion R)) :=
  ContinuousMap.HomotopyEquiv.ofHomotopySquare
    (completedStageZeroHomotopyEquiv R)
    (ContinuousMap.HomotopyEquiv.refl (ClassifyingSpace (StableCompletion.Completion R)))
    (ContinuousMap.HomotopyEquiv.refl (ClassifyingSpace (StableCompletion.Completion R)))
    (classifyingSpaceMapUniversal (completedRetraction R)) (by
      rw [completedStageZeroHomotopyEquiv_toFun]
      change ((classifyingSpaceMapUniversal (completedRetraction R)).comp
        (classifyingSpaceMapUniversal
          (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0))).Homotopic
        ((ContinuousMap.id _).comp (ContinuousMap.id _))
      rw [ContinuousMap.id_comp]
      exact ⟨completedRetractionStageZeroHomotopy R⟩)

/-- No replacement of the retraction map occurs in the homotopy-square construction. -/
@[simp]
lemma completedRetractionHomotopyEquiv_toFun :
    (completedRetractionHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (completedRetraction R) := rfl

/-- The chosen inverse retains exactly the original stage-zero inclusion. -/
lemma completedRetractionHomotopyEquiv_invFun :
    (completedRetractionHomotopyEquiv R).invFun =
      classifyingSpaceMapUniversal (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0) := by
  change (completedStageZeroHomotopyEquiv R).toFun.comp
    ((ContinuousMap.id _).comp (ContinuousMap.id _)) = _
  rw [ContinuousMap.id_comp, ContinuousMap.comp_id, completedStageZeroHomotopyEquiv_toFun]

/-- The genuine basepoint path is the original unitor component, with its prescribed endpoints. -/
def completedRetractionZeroPath :
    Path (classifyingSpaceMapUniversal (completedRetraction R)
      (classifyingSpacePoint (completedTelescopeBase R))) (StableCompletion.zeroPoint R) := by
  rw [classifyingSpaceMapUniversal_point]
  exact classifyingSpacePath
    ((completedRetractionZeroIso R).hom.app (StableCompletion.stageObject R 0))

/-- The retraction carries the original completed base into the genuine zero component. -/
lemma completedRetraction_base_joined :
    Joined (classifyingSpaceMapUniversal (completedRetraction R)
      (classifyingSpacePoint (completedTelescopeBase R))) (StableCompletion.zeroPoint R) :=
  ⟨completedRetractionZeroPath R⟩

/-- The actual zero component of the original completed telescope. -/
abbrev CompletedTelescopeZeroComponent :=
  ↥(pathComponent (classifyingSpacePoint (completedTelescopeBase R)))

/-- The original retraction restricts to a homotopy equivalence of the genuine zero components. -/
def completedRetractionZeroComponentHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (CompletedTelescopeZeroComponent R)
      (StableCompletion.ZeroComponent R) :=
  pathComponentHomotopyEquiv (completedRetractionHomotopyEquiv R)
    (classifyingSpacePoint (completedTelescopeBase R)) (StableCompletion.zeroPoint R)
    (completedRetraction_base_joined R)

/-- The component equivalence keeps exactly the original retraction on underlying points. -/
@[simp]
lemma completedRetractionZeroComponentHomotopyEquiv_val
    (x : CompletedTelescopeZeroComponent R) :
    (completedRetractionZeroComponentHomotopyEquiv R x).val =
      classifyingSpaceMapUniversal (completedRetraction R) x.val := rfl

/-- The component inverse keeps exactly the original completed stage-zero map. -/
@[simp]
lemma completedRetractionZeroComponentHomotopyEquiv_symm_val
    (x : StableCompletion.ZeroComponent R) :
    ((completedRetractionZeroComponentHomotopyEquiv R).symm x).val =
      classifyingSpaceMapUniversal
        (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0) x.val := by
  change (completedRetractionHomotopyEquiv R).invFun x.val = _
  rw [completedRetractionHomotopyEquiv_invFun]
  rfl

/-- The original total retraction map is therefore a weak homotopy equivalence. -/
lemma completedRetraction_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (completedRetraction R)) := by
  rw [← completedRetractionHomotopyEquiv_toFun]
  exact isWeakHomotopyEquivalence_of_homotopyEquiv (completedRetractionHomotopyEquiv R)

end Quillen.FiniteProjectiveModule.StableFreeRight
