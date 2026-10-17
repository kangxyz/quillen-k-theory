/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedPushoutComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeActualMixedFiller

/-! The two proved mixed fillers descend to the original two-chart seed comparison. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.CoefficientBassActualSeedComparison

/-- The original two-chart comparison commutes with the coefficient seed up to homotopy. -/
def comparison {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) :
    Homotopy (boundedFlatCoefficientBassSquareComparison P a ≫
      boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))
      (CoefficientBassSeedPushoutComparison.spanMap P a ≫
        boundedFlatCoefficientBassSecondSquareComparison P a) :=
  CoefficientBassSeedPushoutComparison.comparison P a
    (CoefficientBassNegativeActualMixedFiller.originalComparison P a)

end Quillen.PerfectComplexes.CoefficientBassActualSeedComparison
