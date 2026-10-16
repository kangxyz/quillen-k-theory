/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNativeCube

/-! Strict consumers of the produced original identity cube and its whole three-time quotient. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.PerfectComplexes.CoefficientBassUnitNodes
open Quillen.PerfectComplexes.CoefficientBassUnitScalarCube
open Quillen.PerfectComplexes.CoefficientBassUnitNativeCube
open scoped Topology unitInterval
universe u
namespace QuillenTest.CoefficientBassUnitNativeCube
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

def original_identity_cube : BoundedFlatCoefficientBassIdentityInteriorCube P a :=
  interiorCube P a

theorem entire_cube_level_zero (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    (original_identity_cube P a).level 0 (r, (s, (t, x))) =
      prespectrumSimplexFamily (simplex P a) 0 (scalarCube.{u} ![r, s, t], x) :=
  interiorCube_level_zero P a r s t x

theorem actual_quotient_cylinder (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassComparisonIdentitySquareOfInteriorCube P a
      (interiorCube P a)).level n
        (r, (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) =
      prespectrumSimplexFamily (simplex P a) n (scalarCube.{u} ![r, s, t], x) := rfl

theorem original_cube_structure (n : ℕ) (r s t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (interiorCube P a).level (n + 1)
      (r, (s, (t, (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, a)))).structureMap n x z))) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a)))).structureMap n
          ((interiorCube P a).level n (r, (s, (t, x)))) z :=
  (interiorCube P a).comm n r s t x z

end QuillenTest.CoefficientBassUnitNativeCube
