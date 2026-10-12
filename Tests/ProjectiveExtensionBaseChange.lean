/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.ProjectiveExtensionBaseChangeProjection
public import Mathlib.Data.ZMod.Basic

/-! # Actual actor-changing extension and original Q-square consumers -/
noncomputable section
open CategoryTheory MonoidalCategory Quillen Quillen.FiniteProjectiveModule
open scoped MonoidalLeftAction
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric inflationDirectSumAction
  rightBaseChangeMonoidal rightBaseChangeCoreMonoidal
universe u

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (P : IsoCategory Rᵐᵒᵖ) (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (Subdivision.domainMap (rightBaseChangeExtensionTensorIso f P x).hom).hom =
      (rightBaseChangeTensorIso f P.of x.fiber.unop.left.obj).inv := rfl

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    LocalizedExtensionCategory Rᵐᵒᵖ ⥤ LocalizedExtensionCategory Sᵐᵒᵖ :=
  localizedExtensionBaseChange f

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    localizedExtensionProjection Rᵐᵒᵖ ⋙ (rightBaseChangeExact f).mapQ ≅
      localizedExtensionBaseChange f ⋙ localizedExtensionProjection Sᵐᵒᵖ :=
  localizedExtensionBaseChangeProjectionIso f

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (A : IsoCategory Rᵐᵒᵖ) (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (localizedExtensionBaseChangeProjectionIso f).hom.app (localizedExtensionPair Rᵐᵒᵖ A x) =
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso ((rightBaseChangeExact f).extensionQuotientIso x)).hom := rfl

example :
    localizedExtensionProjection (ZMod 1)ᵐᵒᵖ ⋙ (rightBaseChangeExact (RingHom.id (ZMod 1))).mapQ ≅
      localizedExtensionBaseChange (RingHom.id (ZMod 1)) ⋙
        localizedExtensionProjection (ZMod 1)ᵐᵒᵖ :=
  localizedExtensionBaseChangeProjectionIso (RingHom.id (ZMod 1))
