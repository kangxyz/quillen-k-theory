/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.ModelDoubleCorrection

/-! Regression properties of the original double-Laurent quotient and finite correction. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.GeometricConeInterchange
open Quillen.KTheory.Bass.SchemeNaturalSeed
universe u w

/-- Each class really has an original double-Laurent representative. -/
example (M : Scheme.{u}ᵒᵖ ⥤ Model.{w}) (X : Scheme.{u}ᵒᵖ)
    (y : stableHomotopyGroup
      ((coneFunctor.obj (coneFunctor.obj (M ⋙ prespectrumFunctor))).obj X) 0) :
    ∃ x, (stableHomotopyFunctor 0).map
      (doubleLaurentInclusion (M ⋙ prespectrumFunctor) X) x = y := by
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (doubleLaurentInclusion_zero_epi M X) y

/-- Descent through the four original relations still reaches every double-cone class. -/
example (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ) :
    Epi (doubleLaurentQuotientMap (M ⋙ prespectrumFunctor)
      (fun Y => model_linearZeroGrowth (M.obj Y)) X) := by
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _
    (doubleLaurentInclusion_zero_epi M (op X.unop.obj))
    (doubleLaurentQuotientMap_π (M ⋙ prespectrumFunctor)
      (fun Y => model_linearZeroGrowth (M.obj Y)) X)
