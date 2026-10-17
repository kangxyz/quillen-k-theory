/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows
public import Quillen.Aglib.Topology.Path.ThreeRadialSquares
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily

/-! The prescribed three Laurent squares pasted with their literal boundary path words. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentProjectionScalar
open DoubleSquareScalarPaths

/-- The exact chart-then-polynomial boundary keeps its two independent half clocks. -/
def leftWord := (firstRestriction.symm.trans secondRestriction).trans
  (middleChart.symm.trans lastRestriction)

/-- The opposite boundary has the original reversed composition and nested square clocks. -/
def rightWord := sourceChart.symm.trans
  ((sourceTotal.symm.trans targetTotal).trans targetChart)

/-- Only the three original split-triple squares and explicit path cancellations are used. -/
def scalarComparison : leftWord.Homotopy rightWord :=
  Path.Homotopy.ThreeRadialSquares.paste sourceTotal firstIntermediate middleTotal targetTotal
    sourceChart firstRestriction secondRestriction middleChart lastRestriction targetChart
    firstComparison middleComparison lastComparison

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (u : a ⟶ b)

/-- The Laurent coefficient map of the polynomial coefficient inclusion at the source algebra
`a`. -/
abbrev p := coefficientMap P ((laurentUnderFunctor R).map ((polynomialUnderCoefficient R).app a))
/-- The Laurent coefficient map of the chosen chart `α` at the source algebra `a`. -/
abbrev q := coefficientMap P ((laurentUnderFunctor R).map (α.app a))
/-- The Laurent coefficient map of the polynomial coefficient inclusion at the target algebra
`b`. -/
abbrev p' := coefficientMap P ((laurentUnderFunctor R).map ((polynomialUnderCoefficient R).app b))
/-- The Laurent coefficient map of the chosen chart `α` at the target algebra `b`. -/
abbrev q' := coefficientMap P ((laurentUnderFunctor R).map (α.app b))
/-- The original coefficient map of the Laurent extension of `u`. -/
abbrev aMap := coefficientMap P ((laurentUnderFunctor R).map u)
/-- The original coefficient map of `u` after polynomial extension and then Laurent extension. -/
abbrev bMap := coefficientMap P ((laurentUnderFunctor R).map ((polynomialUnderFunctor R).map u))
/-- The original coefficient map of `u` after two Laurent extensions. -/
abbrev cMap := coefficientMap P ((laurentUnderFunctor R).map ((laurentUnderFunctor R).map u))

theorem polynomial_square : bMap P u ≫ p P (a := a) = p' P (b := b) ≫ aMap P u :=
  coefficientMap_naturality P
    (whiskerRight (polynomialUnderCoefficient R) (laurentUnderFunctor R)) u

theorem chart_square : cMap P u ≫ q P α (a := a) = q' P α (b := b) ≫ bMap P u :=
  coefficientMap_naturality P (whiskerRight α (laurentUnderFunctor R)) u

/-- The normalized triple source reference for the original Laurent projection square. -/
abbrev reference := NormalizedTripleSimplex.sourceMap (cMap P u) (q P α (a := a)) (p P (a := a))

/-- The eighteen full merged-square reference nodes with the original polynomial and chart
squares. -/
def nodes : Fin 18 → CommonReferenceNerve.Node (reference P α u) :=
  DoubleSquareMergedSimplex.nodes (p P (a := a)) (q P α (a := a))
    (p' P (b := b)) (q' P α (b := b)) (aMap P u) (bMap P u) (cMap P u)
    (polynomial_square P u) (chart_square P α u)

/-- A continuous Laurent-input parameter surface with the fixed old path-word boundary. -/
def family : C(I × I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P α u)))|) :=
  (CommonReferenceNerve.parameter (reference P α u) (nodes P α u)).comp
    scalarComparison.toHomotopy.toContinuousMap

theorem family_zero (s : I) : family P α u (0, s) =
    CommonReferenceNerve.parameter (reference P α u) (nodes P α u) (leftWord s) :=
  congrArg (CommonReferenceNerve.parameter (reference P α u) (nodes P α u))
    (scalarComparison.apply_zero s)

theorem family_one (s : I) : family P α u (1, s) =
    CommonReferenceNerve.parameter (reference P α u) (nodes P α u) (rightWord s) :=
  congrArg (CommonReferenceNerve.parameter (reference P α u) (nodes P α u))
    (scalarComparison.apply_one s)

theorem family_bottom (r : I) : family P α u (r, 0) =
    CommonReferenceNerve.parameter (reference P α u) (nodes P α u) (StdSimplex.single 11) :=
  congrArg (CommonReferenceNerve.parameter (reference P α u) (nodes P α u))
    (scalarComparison.source r)

theorem family_top (r : I) : family P α u (r, 1) =
    CommonReferenceNerve.parameter (reference P α u) (nodes P α u) (StdSimplex.single 17) :=
  congrArg (CommonReferenceNerve.parameter (reference P α u) (nodes P α u))
    (scalarComparison.target r)

end Quillen.PerfectComplexes.CoefficientBassLaurentProjectionScalar
