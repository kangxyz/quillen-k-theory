/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveExtensionLinear
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-! # Consumer of the actual quotient lineator and both coherence proofs -/
noncomputable section
open CategoryTheory MonoidalCategory
open Quillen.FiniteProjectiveModule
universe u
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] MonoidalLeftAction.trivial

example : (exactStructure R).extensionProjection.LaxLeftLinear (IsoCategory R) :=
  extensionProjectionLinear R

example : (exactStructure (Matrix (Fin 2) (Fin 2) ℤ)).extensionProjection.LaxLeftLinear
    (IsoCategory (Matrix (Fin 2) (Fin 2) ℤ)) := extensionProjectionLinear _

example : (exactStructure (ZMod 1)).extensionProjection.LaxLeftLinear (IsoCategory (ZMod 1)) :=
  extensionProjectionLinear _
