/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassMovingSquarePause
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositionCharts

/-! Both fixed native Bass chart squares retain the exact scalar pause and quotient parameter. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The complete positive Bass chart is the actual paused common-simplex surface. -/
theorem plusChart_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (simplex P (underToLaurent R) u v) n
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
      (boundedFlatCoefficientBassCompositionPlusChart P u v).level n (r, (s, x)) :=
  pausedSquare_native P (underToLaurent R) u v n r s x

/-- The complete negative Bass chart uses its own inverse-coordinate source simplex. -/
theorem minusChart_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (simplex P (underToLaurentInvert R) u v) n
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
      (boundedFlatCoefficientBassCompositionMinusChart P u v).level n (r, (s, x)) :=
  pausedSquare_native P (underToLaurentInvert R) u v n r s x

end Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
