/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex

/-! Whole original polynomial and Laurent-chart square families before any overlap restriction. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientSquareFamilies
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

abbrev polynomialSource := NativeSquareFiveSimplex.source
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)
abbrev polynomialNodes := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)
  (polynomialProjection P b) (coefficientMap P w)
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) w)
abbrev polynomialSimplex := NativeSquareFiveSimplex.simplex
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)
  (polynomialProjection P b) (coefficientMap P w)
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) w)

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
abbrev chartSource := NativeSquareFiveSimplex.source
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
abbrev chartNodes := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map w))
  (coefficientTransformation_naturality P α w)
abbrev chartSimplex := NativeSquareFiveSimplex.simplex
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map w))
  (coefficientTransformation_naturality P α w)

/-- The whole original polynomial square, on every original source input and level. -/
theorem polynomial_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (polynomialSimplex P w) n
      (NativeSquareFiveSimplex.parameter t, x) =
      (boundedFlatCoefficientPolynomialSquareHomotopy P w).level n (t, x) :=
  NativeSquareFiveSimplex.native _ _ _ _ _ n t x

/-- The whole positive square accepts arbitrary polynomial-chart inputs, before projection. -/
theorem plus_native (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (chartSimplex P w (underToLaurent R)) n
      (NativeSquareFiveSimplex.parameter s, x) =
      (boundedFlatCoefficientPlusSquareHomotopy P w).level n (s, x) :=
  NativeSquareFiveSimplex.native _ _ _ _ _ n s x

/-- The separate inverse square likewise retains every arbitrary polynomial-chart input. -/
theorem minus_native (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (chartSimplex P w (underToLaurentInvert R)) n
      (NativeSquareFiveSimplex.parameter s, x) =
      (boundedFlatCoefficientMinusSquareHomotopy P w).level n (s, x) :=
  NativeSquareFiveSimplex.native _ _ _ _ _ n s x

end Quillen.PerfectComplexes.CoefficientSquareFamilies
