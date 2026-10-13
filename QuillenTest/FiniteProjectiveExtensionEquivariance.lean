/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveExtensionEquivariance

/-! # The actual total extension action and its projection-compatible natural isomorphism -/
noncomputable section
open CategoryTheory MonoidalCategory
open Quillen.FiniteProjectiveModule
universe u
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction

example : MonoidalLeftAction (IsoCategory R) (exactStructure R).ExtensionTotal :=
  extensionDirectSumAction R

example (S : IsoCategory R) :
    MonoidalLeftAction.actionLeft (exactStructure R).ExtensionTotal S ⋙
      (exactStructure R).extensionProjection ≅ (exactStructure R).extensionProjection :=
  directSumProjectionIso R S
