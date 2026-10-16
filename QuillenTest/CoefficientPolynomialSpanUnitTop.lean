/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitTop

/-! The complete actual polynomial-span-unit top face keeps the original cylinder, including
level zero, and retains a structure coordinate independent of both square parameters. -/

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
namespace QuillenTest.CoefficientPolynomialSpanUnitTop
open Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitTop
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

theorem original_top_level_zero (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    prespectrumSimplexFamily (simplex P a) 0 (topParameter.{u} (r, t), x) =
      ((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
        (boundedFlatCoefficientBassSquareComparison P a)).level 0
        (r, HomotopyPushout.cylinder (polynomialMap P a) (polynomialMap P a) 0 (t, x)) :=
  top_native P a 0 r t x

theorem original_identity_endpoint (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (topParameter.{u} (1, t), x) =
      (comparisonMap P a).map n
        (HomotopyPushout.cylinder (polynomialMap P a) (polynomialMap P a) n (t, x)) := by
  exact (top_native P a n 1 t x).trans
    (((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
      (comparisonMap P a)).at_one n
      (HomotopyPushout.cylinder (polynomialMap P a) (polynomialMap P a) n (t, x)))

theorem independent_structure (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) (n + 1)
      (topParameter.{u} (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a)))).structureMap n
          (((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
            (comparisonMap P a)).level n
              (r, HomotopyPushout.cylinder
                (polynomialMap P a) (polynomialMap P a) n (t, x))) z := by
  exact (prespectrumSimplexFamily_structure (simplex P a) n (topParameter.{u} (r, t)) x z).trans
    (congrArg (fun y ↦ (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).structureMap n y z)
      (top_native P a n r t x))

end QuillenTest.CoefficientPolynomialSpanUnitTop
