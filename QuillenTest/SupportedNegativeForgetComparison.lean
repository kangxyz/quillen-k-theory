/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedNegativeTelescopeForget

/-! # Inverse original comparisons retain the actual support-forgetting maps -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The inverse finite comparison gives the original supported negative map, including degree zero.
-/
example (i : ℕ) (a : Under R) :
    (boundedFlatCoefficientSupportedNegativeKComparison f i).inv.app a ≫
      (Bass.supportedNegativeKForgetNat i).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) =
    (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatCoefficientSupportedBassForget f i).app a) ≫
      (boundedFlatCoefficientAmbientNegativeKComparison Q i).inv.app a := by
  apply ((boundedFlatCoefficientSupportedNegativeKComparison f i).app a).inv_comp_eq.mpr
  erw [← Category.assoc]
  exact ((boundedFlatCoefficientAmbientNegativeKComparison Q i).app a).eq_comp_inv.mpr
    (boundedFlatCoefficientSupportedNegativeKComparison_forget_app f i a)

/-- The same original negative map is retained by the inverse actual telescope comparisons. -/
example [CompactSpace P.left] [QuasiSeparatedSpace Q.left] (i : ℕ) (a : Under R) :
    (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).inv.app a ≫
      (Bass.supportedNegativeKForgetNat i).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) =
    (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a) ≫
      (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).inv.app a := by
  apply ((boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).app a).inv_comp_eq.mpr
  erw [← Category.assoc]
  exact ((boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).app a).eq_comp_inv.mpr
    (boundedFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app f i a)
