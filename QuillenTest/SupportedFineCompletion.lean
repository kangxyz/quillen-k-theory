/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedConnectiveTelescopeComparison

/-! Regression and core-axiom checks for the original supported fine completion. -/
noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
namespace Quillen.PerfectComplexes
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (i : ℕ) (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedBassTransition f i).app a)) :=
  boundedFlatCoefficientSupportedBassTransition_isIso_of_le f i a d hd

example (i : ℕ) (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedBassTelescopeInclusion f i).app a)) :=
  boundedFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le f i a d hd

example (a : Under R) :
    (boundedFlatCoefficientSupportedKTelescopeComparison f 0).hom.app a =
      (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f 0).hom.app a :=
  boundedFlatCoefficientSupportedKTelescopeComparison_zero_hom_app f a

#print axioms boundedFlatCoefficientSupportedPolynomialIso_corner
#print axioms boundedFlatCoefficientSupportedRestrictedMiddle_iteratedK_exact
#print axioms boundedFlatCoefficientSupportedNegativeMiddle_exact
#print axioms boundedFlatCoefficientSupportedBottomChart_exact
#print axioms boundedFlatCoefficientSupportedBassTransition_isIso_of_le
#print axioms boundedFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le
#print axioms boundedFlatCoefficientSupportedNegativeKTelescopeComparison
#print axioms boundedFlatCoefficientSupportedNegativeKTelescopeComparison_π
#print axioms boundedFlatCoefficientSupportedKTelescopeComparison
end Quillen.PerfectComplexes
