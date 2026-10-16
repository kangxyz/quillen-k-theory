/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNativeFaces

/-! Strict consumers retain entire original faces, the actual level-zero source, and independent
structure time in the common forty-eight-node native family. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.PerfectComplexes.CoefficientBassUnitNodes
open Quillen.PerfectComplexes.CoefficientBassUnitScalarEdges
open Quillen.PerfectComplexes.CoefficientBassUnitNativeFaces
open scoped Topology unitInterval
universe u
namespace QuillenTest.CoefficientBassUnitNativeFaces
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

theorem original_inverse_face (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (minusParameter (r, s), x) =
      (boundedFlatCoefficientBassIdentityMinusChart P a).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  minus_native P a n r s x

theorem original_top_zero (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    prespectrumSimplexFamily (simplex P a) 0 (topParameter.{u} (r, t), x) =
      ((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
        (boundedFlatCoefficientBassSquareComparison P a)).level 0
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) 0 (t, x)) :=
  top_native P a 0 r t x

theorem independent_structure_time (n : ℕ) (r s z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) (n + 1)
      (plusParameter (r, s), (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, a)))).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a)))).structureMap n
          (prespectrumSimplexFamily (simplex P a) n (plusParameter (r, s), x)) z :=
  family_structure P a n _ x z

end QuillenTest.CoefficientBassUnitNativeFaces
