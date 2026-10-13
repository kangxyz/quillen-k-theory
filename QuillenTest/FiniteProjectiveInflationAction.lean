/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveInflationAction
import Mathlib.Data.Matrix.Basic

/-! # Noncommutative right-module consumers of the direct-sum inflation action -/
noncomputable section
open CategoryTheory MonoidalCategory
open Quillen.FiniteProjectiveModule
universe u
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction

example (R : Type u) [Ring R] :
    MonoidalLeftAction (IsoCategory Rᵐᵒᵖ) (exactStructure Rᵐᵒᵖ).InflationCategory :=
  inflationDirectSumAction Rᵐᵒᵖ

example : MonoidalLeftAction (IsoCategory (Matrix (Fin 2) (Fin 2) ℤ))
    (exactStructure (Matrix (Fin 2) (Fin 2) ℤ)).InflationCategory := inferInstance
