/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitSimplex

/-! The actual product middle reaches the unchanged, unpaused original Bass cylinder. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace QuillenTest.CoefficientPolynomialSpanUnitSimplex
open Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitSimplex
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

theorem middle_identity_endpoint (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleSimplex P a) n (middleParameter.{u} (1, s), x) =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) := by
  rw [middle_native, (boundedFlatCoefficientIdentityHomotopy P a).at_one]
  rfl

theorem middle_original_start (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleSimplex P a) n (middleParameter.{u} (0, s), x) =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n
          (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P (𝟙 a))).map n x)) := by
  rw [middle_native, (boundedFlatCoefficientIdentityHomotopy P a).at_zero]

end QuillenTest.CoefficientPolynomialSpanUnitSimplex
