/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.KTheory.Plus.ProjectiveExtensionBaseChangeIdentityNaturality
public import Mathlib.Data.ZMod.Basic

/-! # Full original identity-entry naturality and based-triangle consumers -/
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

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionBaseChange f ≅
      completionBaseChange f ⋙ completionIdentityEntry Sᵐᵒᵖ :=
  completionIdentityBaseChangeNatIso f

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (U V : GroupCompletionCategory Rᵐᵒᵖ) (h : U ⟶ V) :
    (localizedExtensionBaseChange f).map ((completionIdentityEntry Rᵐᵒᵖ).map h) ≫
      (completionIdentityBaseChangeIso f V).hom =
    (completionIdentityBaseChangeIso f U).hom ≫
      (completionIdentityEntry Sᵐᵒᵖ).map ((completionBaseChange f).map h) :=
  (completionIdentityBaseChangeNatIso f).hom.naturality h

example : completionIdentityEntry (ZMod 1)ᵐᵒᵖ ⋙
      localizedExtensionBaseChange (RingHom.id (ZMod 1)) ≅
    completionBaseChange (RingHom.id (ZMod 1)) ⋙
      completionIdentityEntry (ZMod 1)ᵐᵒᵖ :=
  completionIdentityBaseChangeNatIso _
