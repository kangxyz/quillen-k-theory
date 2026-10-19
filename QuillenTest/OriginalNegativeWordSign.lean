/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.ModelLaurentWordQuotient
import Quillen.KTheory.Bass.SchemeConjugationAllSign

/-! Regression properties for original Laurent representatives and finite negative words. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.GeometricConeInterchange
open Quillen.KTheory.Bass.SchemeNaturalSeed
universe u w

/-- Each original finite cone class is represented on the actual n-fold Laurent chart. -/
example (M : Scheme.{u}ᵒᵖ ⥤ Model.{w}) (n : ℕ) (X : Scheme.{u}ᵒᵖ)
    (y : stableHomotopyGroup
      ((Quillen.KTheory.Bass.FiniteConeTopology.iterate
        PolynomialLaurent.GlobalIndex.squareFunctor n (M ⋙ prespectrumFunctor)).obj X) 0) :
    ∃ x, (stableHomotopyFunctor 0).map
      (laurentInclusion n (M ⋙ prespectrumFunctor) X) x = y := by
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (laurentInclusion_zero_epi (M ⋙ prespectrumFunctor)
      (fun Y => model_linearZeroGrowth (M.obj Y)) n X) y

/-- The prescribed original finite correction fixes each class in its actual negative degree. -/
example (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (S : QuasiCompactSchemes.{u}ᵒᵖ → Prop)
    (hL : ∀ X, S X → S (PolynomialLaurent.Relative.laurentFunctor.op.obj X))
    (hτ : ∀ X, S X → PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (M ⋙ prespectrumFunctor)) X = -𝟙 _)
    (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ) (hX : S X)
    (y : stableHomotopyGroup
      (((Quillen.KTheory.Bass.strictDiagramIterate
        PolynomialLaurent.GlobalIndex.squareFunctor n).obj
          (M ⋙ prespectrumFunctor)).obj (op X.unop.obj)) (-(n : ℤ))) :
    (finiteStageStableIso M n (op X.unop.obj) (-(n : ℤ))).hom y = y := by
  rw [finiteStageStableIso_neg_nat_id S M hτ hL n X hX]
  rfl
