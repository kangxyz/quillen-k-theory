/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitBottom

/-! The original bottom product keeps the unpaused Bass cylinder and native level zero. -/

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
namespace QuillenTest.CoefficientBassUnitBottom
open Quillen.PerfectComplexes.CoefficientBassUnitBottom
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

theorem terminal_original_cylinder (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (parameter.{u} (1, t), x) =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  exact (native P a n 1 t x).trans
    ((boundedFlatCoefficientLaurentIdentityHomotopy P a).at_one n _)

theorem positive_level_zero (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    prespectrumSimplexFamily (simplex P a) 0
      (Quillen.SimplexParameters.binaryPath (k := 14) 6 7 8 r, x) =
      (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentIdentityHomotopy P a)).level 0
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) 0 (0, x)) := by
  exact (congrArg (fun z ↦ prespectrumSimplexFamily (simplex P a) 0 (z, x))
    (parameter_left.{u} r).symm).trans (native P a 0 r 0 x)

end QuillenTest.CoefficientBassUnitBottom
