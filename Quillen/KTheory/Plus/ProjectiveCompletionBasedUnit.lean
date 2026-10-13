/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionUnitHomotopy
public import Quillen.CategoryTheory.TheoremB.StructuredUniverseComparison
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Exact original-basepoint track of the completed-model comparison -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u
namespace Quillen.FiniteProjectiveModule.StableFreeRight
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- The original unit correction and the chosen completed retraction have exactly
the same component at the original zero object. -/
theorem telescopeUnitCompletionHom_base :
    (telescopeUnitCompletionHom R).app (projectiveTelescopeBase R) =
      (completedRetractionZeroIso R).hom.app (StableCompletion.stageObject R 0) := by
  change (telescopeUnitCompletionHom R).app
    ⟨0, AsSmall.up.obj (𝟙_ (IsoCategory Rᵐᵒᵖ))⟩ = _
  rw [telescopeUnitCompletionHom_app]
  dsimp only [completedRetractionZeroIso, Iso.trans_hom, NatTrans.comp_app,
    completedInverseFiberUnitHom, Localization.unitFirstCoordinateHom,
    Localization.firstCoordinateUnitor, rankOnePower, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  erw [unitors_equal]
  congr 1
  simp only [completedRetractionStageIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Grothendieck.ιCompMap,
    NatIso.ofComponents_hom_app, Iso.refl_hom, eqToIso.hom, eqToHom_app]
  erw [(originalCompletedRetraction R).map_id, Category.id_comp]

private theorem path_mpr_apply {Z : Type (u + 1)} [TopologicalSpace Z]
    {a b c : Z} (h : a = b) (p : Path b c) (t : unitInterval) :
    (Eq.mpr (congrArg (fun z ↦ Path z c) h) p) t = p t := by
  cases h
  rfl

/-- At the original base vertex, the actual infinite comparison homotopy
traverses the original completed unitor edge. -/
theorem telescopeUnitCompletionHomotopy_base (t : unitInterval) :
    telescopeUnitCompletionHomotopy R (t, classifyingSpacePoint (projectiveTelescopeBase R)) =
      completedRetractionZeroPath R t := by
  change classifyingSpaceUniversalHomotopy (telescopeUnitCompletionHom R)
      (t, classifyingSpacePoint (projectiveTelescopeBase R)) = _
  rw [classifyingSpaceUniversalHomotopy_vertex_track, telescopeUnitCompletionHom_base]
  exact (path_mpr_apply
    (classifyingSpaceMapUniversal_point (completedRetraction R) (completedTelescopeBase R))
    (classifyingSpacePath ((completedRetractionZeroIso R).hom.app
      (StableCompletion.stageObject R 0))) t).symm

/-- The specified original-basepoint tracks agree pointwise, with their actual endpoints. -/
theorem telescopeUnitCompletionBasePath_apply (t : unitInterval) :
    telescopeUnitCompletionBasePath R t = completedRetractionZeroPath R t :=
  telescopeUnitCompletionHomotopy_base R t

/-- Identify the specified comparison track's endpoints by the exact original
unit/base formulas, retaining its underlying path. -/
def telescopeUnitCompletionBasePathAligned :
    Path (classifyingSpaceMapUniversal (completedRetraction R)
      (classifyingSpacePoint (completedTelescopeBase R))) (StableCompletion.zeroPoint R) :=
  (telescopeUnitCompletionBasePath R).cast
    (congrArg (classifyingSpaceMapUniversal (completedRetraction R))
      (classifyingSpaceMapUniversal_point
        (TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1)) (projectiveTelescopeBase R))).symm
    (classifyingSpaceMapUniversal_point (completionFunctor R) (projectiveTelescopeBase R)).symm

/-- The original comparison track equals the chosen completed-retraction track,
after the specified original endpoint identifications. -/
theorem telescopeUnitCompletionBasePathAligned_eq :
    telescopeUnitCompletionBasePathAligned R = completedRetractionZeroPath R := by
  apply Path.ext
  funext t
  exact telescopeUnitCompletionBasePath_apply R t

end Quillen.FiniteProjectiveModule.StableFreeRight
