/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeBoundaryCorrection
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentFirstBoundary

/-! Regression for the unchanged current classes and the image-only N₁-to-N₂ gate. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ParameterFullCurrentNull
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    currentNegativeConnecting f 0 a = currentFirstNegativeConnecting f a := by
  rfl

example (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (hfix : ∀ x,
      (GlobalSupportedParameterCoefficient.negativeClassCorrection f 2 a).hom
        (boundedFlatCoefficientNegativeLocalizationConnecting f 1 a x) =
      boundedFlatCoefficientNegativeLocalizationConnecting f 1 a x) :
    currentNegativeConnecting f 1 a =
      boundedFlatCoefficientNegativeLocalizationConnecting f 1 a := by
  apply (currentNegativeConnecting_one_eq_original_iff f a).2
  ext x
  exact hfix x

example (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (hfix : ∀ x,
      (GlobalSupportedParameterCoefficient.negativeClassCorrection f 2 a).hom
        (boundedFlatCoefficientNegativeLocalizationConnecting f 1 a x) =
      boundedFlatCoefficientNegativeLocalizationConnecting f 1 a x) :
    Function.Exact (currentNegativeConnecting f 1 a)
      ((Bass.supportedNegativeKForgetNat 2).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)) := by
  have h := (currentNegativeConnecting_one_eq_original_iff f a).2 (by
    ext x
    exact hfix x)
  rw [h]
  exact boundedFlatCoefficientNegativeLocalizationConnecting_exact_supported f 1 a
