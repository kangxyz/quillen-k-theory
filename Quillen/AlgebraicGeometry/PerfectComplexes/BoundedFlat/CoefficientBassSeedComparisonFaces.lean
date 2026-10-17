/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassActualSeedComparison

/-! Exact whole chart and cylinder faces of the chosen actual seed comparison. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedComparisonFaces
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The positive polynomial chart retains the original coefficient seed track at every time. -/
theorem comparison_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (CoefficientBassActualSeedComparison.comparison P a).level n
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
        ((underToLaurent R).app a)).symm.level n (r, x) := by
  dsimp only [CoefficientBassActualSeedComparison.comparison,
    CoefficientBassSeedPushoutComparison.comparison]
  dsimp only [Homotopy.cast]
  exact HomotopyPushout.descSquareHomotopy_inl _ _ _ _ _ n r x

/-- The inverse polynomial chart retains its distinct original coefficient seed track. -/
theorem comparison_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (CoefficientBassActualSeedComparison.comparison P a).level n
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
        ((underToLaurentInvert R).app a)).symm.level n (r, x) := by
  dsimp only [CoefficientBassActualSeedComparison.comparison,
    CoefficientBassSeedPushoutComparison.comparison]
  dsimp only [Homotopy.cast]
  exact HomotopyPushout.descSquareHomotopy_inr _ _ _ _ _ n r x

/-- The whole overlap retains the actual chosen mixed-filler square and both clocks. -/
theorem comparison_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassActualSeedComparison.comparison P a).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) =
      (CoefficientBassSeedPushoutComparison.descPasting P a
        (CoefficientBassNegativeActualMixedFiller.originalComparison P a)).toSquare.level n
          (r, (s, x)) := by
  dsimp only [CoefficientBassActualSeedComparison.comparison,
    CoefficientBassSeedPushoutComparison.comparison]
  dsimp only [Homotopy.cast]
  exact HomotopyPushout.descSquareHomotopy_cylinder _ _ _ _ _ n r s x

end Quillen.PerfectComplexes.CoefficientBassSeedComparisonFaces
