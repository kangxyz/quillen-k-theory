/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquareSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitCharts

/-! Both original Laurent unit charts retain their entire two-parameter native square,
including their original coefficient-identity transports and the degree-zero loop level. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace QuillenTest.OriginalUnitSquareSimplex
open Quillen.PerfectComplexes.OriginalUnitSquareSimplex
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

theorem plus_whole_chart (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (simplex (laurentPlus P a)) n (squareParameter (r, s), x) =
      (boundedFlatCoefficientPlusIdentitySquare P a).level n (r, (s, x)) :=
  square_native (laurentPlus P a) n r s x

theorem minus_whole_chart (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (simplex (laurentMinus P a)) n (squareParameter (r, s), x) =
      (boundedFlatCoefficientMinusIdentitySquare P a).level n (r, (s, x)) :=
  square_native (laurentMinus P a) n r s x

theorem minus_level_zero (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space 0) :
    prespectrumSimplexFamily (simplex (laurentMinus P a)) 0 (squareParameter (r, s), x) =
      (boundedFlatCoefficientMinusIdentitySquare P a).level 0 (r, (s, x)) :=
  square_native (laurentMinus P a) 0 r s x

theorem plus_independent_structure (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (simplex (laurentPlus P a)) (n + 1)
      (squareParameter (r, s), (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (polynomialUnderFunctor R).obj a)))).structureMap n x t) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a)))).structureMap n
          ((boundedFlatCoefficientPlusIdentitySquare P a).level n (r, (s, x))) t := by
  rw [family_structure, square_native]
  rfl

#print axioms Quillen.PerfectComplexes.OriginalUnitSquareSimplex.square_native

end QuillenTest.OriginalUnitSquareSimplex
