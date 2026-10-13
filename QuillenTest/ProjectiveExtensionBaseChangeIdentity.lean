/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.KTheory.Plus.ProjectiveExtensionBaseChangeIdentity

/-! # Original identity-entry and rank-zero triangle consumers -/
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
universe u

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (U : GroupCompletionCategory Rᵐᵒᵖ) :
    (localizedExtensionBaseChange f).obj ((completionIdentityEntry Rᵐᵒᵖ).obj U) ≅
      (completionIdentityEntry Sᵐᵒᵖ).obj ((completionBaseChange f).obj U) :=
  completionIdentityBaseChangeIso f U

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (localizedExtensionBaseChangeProjectionIso f).hom.app
        ((completionIdentityEntry Rᵐᵒᵖ).obj (StableCompletion.stageObject R 0)) ≫
      (localizedExtensionProjection Sᵐᵒᵖ).map (completionIdentityBaseChangeZeroIso f).hom ≫
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom.app (StableCompletion.stageObject S 0) =
    (rightBaseChangeExact f).mapQ.map
        ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom.app (StableCompletion.stageObject R 0)) ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject).hom :=
  completionIdentityBaseChangeZeroIso_triangle f
