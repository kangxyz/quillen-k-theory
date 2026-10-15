/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PolynomialMovingBasis

/-! The whole original polynomial composition square before native span-cylinder pasting. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMComponents
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The actual polynomial moving-square boundary is built from its three unchanged tracks. -/
theorem polynomial_boundary_lift : HomotopyLift (polynomialSimplex P u v)
    DoubleSquareScalarPaths.coefficientBoundaryParameter
    (boundedFlatCoefficientPolynomialCompositionBoundary P u v) :=
  HomotopyLift.boundaryOfComparison _ (polynomial_target_path P u v)
    (polynomial_direct_path P u v) (polynomial_source_path P u v)
    (polynomial_comparison_lift P u v)

/-- Every original moving-square parameter and every level is evaluated in the actual diagram. -/
theorem polynomial_moving_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (polynomialSimplex P u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s), x) =
      (boundedFlatCoefficientPolynomialCompositionSquare P u v).level n (r, (s, x)) :=
  HomotopyLift.toSquare _ (polynomial_boundary_lift P u v) n r s x

/-- The original positive chart postcomposition, before any common-reference transport. -/
def plusSimplex := (polynomialSimplex P u v).postcomp
  (BassH0Merge.normalizedMap (laurentPlus P c))

/-- The separate original inverse-chart postcomposition of the same native polynomial square. -/
def minusSimplex := (polynomialSimplex P u v).postcomp
  (BassH0Merge.normalizedMap (laurentMinus P c))

/-- The complete positive moving component retains the original polynomial square and chart map. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (plusSimplex P u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s), x) =
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c)).map n
      ((boundedFlatCoefficientPolynomialCompositionSquare P u v).level n (r, (s, x))) := by
  rw [plusSimplex, prespectrumSimplexFamily_postcomp, polynomial_moving_native]
  rfl

/-- The inverse moving component retains its original reversal of the path coordinate. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (minusSimplex P u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm s), x) =
    (boundedFlatPerfectPrespectrumMap (laurentMinus P c)).map n
      ((boundedFlatCoefficientPolynomialCompositionSquare P u v).level n
        (r, (unitInterval.symm s, x))) := by
  rw [minusSimplex, prespectrumSimplexFamily_postcomp, polynomial_moving_native]
  rfl

end Quillen.PerfectComplexes.BassMComponents
