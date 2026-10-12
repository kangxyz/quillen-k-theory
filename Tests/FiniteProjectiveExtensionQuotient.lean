/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveExtensionQuotient

/-! # Direct-sum extension quotient invariance over arbitrary rings -/
noncomputable section
open CategoryTheory
open Quillen.FiniteProjectiveModule
universe u
variable (R : Type u) [Ring R]

example (S : IsoCategory R) (x : (exactStructure R).ExtensionTotal) :
    ((exactStructure R).extensionQuotientData (directSumExtensionObject R S x)).obj ≅
      ((exactStructure R).extensionQuotientData x).obj := directSumExtensionQuotientIso R S x
