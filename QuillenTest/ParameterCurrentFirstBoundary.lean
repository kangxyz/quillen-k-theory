/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentFirstBoundary

/-! Regression for the original two arrows adjacent to the current K₀-to-N₁ boundary. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ParameterFullCurrentNull
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Function.Exact ((boundedFlatCoefficientOriginalNegativeKRestriction f 0).app a)
      (currentFirstNegativeConnecting f a) := by
  rw [currentFirstNegativeConnecting_eq_original]
  exact boundedFlatCoefficientNegativeLocalizationConnecting_exact_open f 0 a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Function.Exact (currentFirstNegativeConnecting f a)
      ((Bass.supportedNegativeKForgetNat 1).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)) := by
  rw [currentFirstNegativeConnecting_eq_original]
  exact boundedFlatCoefficientNegativeLocalizationConnecting_exact_supported f 0 a
