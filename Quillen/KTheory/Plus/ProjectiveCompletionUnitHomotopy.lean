/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionUnit
public import Quillen.KTheory.Plus.ProjectiveCompletionRetractionHomotopy

/-! # The original unit-preserving completed-model comparison -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u
namespace Quillen.FiniteProjectiveModule.StableFreeRight
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  projectiveTelescopeAction
variable (R : Type u) [Ring R]

/-- The unit lift retains the actual original zero object. -/
theorem telescopeUnit_base :
    (TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1)).obj
      (projectiveTelescopeBase R) = completedTelescopeBase R := rfl

/-- The actual original completion map is homotopic to the original lifted unit
followed by the genuine completed retraction. -/
def telescopeUnitCompletionHomotopy :
    ((classifyingSpaceMapUniversal (completedRetraction R)).comp
      (classifyingSpaceMapUniversal
        (TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1)))).Homotopy
      (classifyingSpaceMapUniversal (completionFunctor R)) :=
  (classifyingSpaceUniversalHomotopy (telescopeUnitCompletionHom R)).cast
    (classifyingSpaceMapUniversal_comp _ _) rfl

/-- The prescribed comparison carries a specified original-basepoint track. -/
def telescopeUnitCompletionBasePath :
    Path ((classifyingSpaceMapUniversal (completedRetraction R))
      ((classifyingSpaceMapUniversal (TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1)))
        (classifyingSpacePoint (projectiveTelescopeBase R))))
      ((classifyingSpaceMapUniversal (completionFunctor R))
        (classifyingSpacePoint (projectiveTelescopeBase R))) :=
  (telescopeUnitCompletionHomotopy R).evalAt (classifyingSpacePoint (projectiveTelescopeBase R))

/-- The other side of the common-model zigzag retains the original localization unit exactly. -/
theorem telescopeUnit_interchange_unit :
    TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1) ⋙
      (projectiveTelescopeInterchange R).functor =
      GroupCompletion.Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ)
        (D := ProjectiveTelescope R) :=
  TranslationTelescope.telescopeUnit_interchange (freeIso Rᵐᵒᵖ 1)

end Quillen.FiniteProjectiveModule.StableFreeRight
