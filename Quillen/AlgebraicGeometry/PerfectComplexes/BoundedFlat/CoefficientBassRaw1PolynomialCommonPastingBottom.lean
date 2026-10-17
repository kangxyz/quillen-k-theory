/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingBottomPaths
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingBottomSquares
public import Quillen.Aglib.Topology.Path.ThreeRadialSquaresMapEvaluation

/-! The complete chosen polynomial paste retains the fixed original Laurent18 bottom. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingBottom
open CoefficientBassRaw1PolynomialTripleRoutes
open CoefficientBassRaw1PolynomialCommonPastingPaths
open CoefficientBassRaw1PolynomialCommonPastingBottomPaths
open CoefficientBassRaw1PolynomialCommonPastingBottomSquares
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b) (negative : Bool)

/-- Every interior point of the full bottom is the unchanged Laurent18 scalar comparison. -/
theorem family_bottom (r s : I) :
    CoefficientBassRaw1PolynomialCommonPasting.family P α f negative ![r, s, 0] =
      bottomMap P α f negative
        (CoefficientBassLaurentProjectionScalar.scalarComparison (r, s)) := by
  exact Path.Homotopy.ThreeRadialSquares.paste_eval_compare
    (fun g : C(I, CoefficientBassRaw1PolynomialCommonSheet.carrier
      P α (chartChoice negative) f) ↦ g 0) (bottomMap P α f negative)
    (radialA P α f negative)
    (radialB P α f negative)
    (radialC P α f negative)
    (radialD P α f negative)
    (capX P α f negative)
    (capY P α f negative)
    (capZ P α f negative)
    (capW P α f negative)
    (capV P α f negative)
    (capU P α f negative)
    DoubleSquareScalarPaths.sourceTotal
    DoubleSquareScalarPaths.firstIntermediate
    DoubleSquareScalarPaths.middleTotal
    DoubleSquareScalarPaths.targetTotal
    DoubleSquareScalarPaths.sourceChart
    DoubleSquareScalarPaths.firstRestriction
    DoubleSquareScalarPaths.secondRestriction
    DoubleSquareScalarPaths.middleChart
    DoubleSquareScalarPaths.lastRestriction
    DoubleSquareScalarPaths.targetChart
    (CoefficientBassRaw1PolynomialCommonPasting.firstComparison P α f negative)
    (CoefficientBassRaw1PolynomialCommonPasting.middleComparison P α f negative)
    (CoefficientBassRaw1PolynomialCommonPasting.lastComparison P α f negative)
    DoubleSquareScalarPaths.firstComparison
    DoubleSquareScalarPaths.middleComparison
    DoubleSquareScalarPaths.lastComparison
    (radialA_bottom P α f negative)
    (radialB_bottom P α f negative)
    (radialC_bottom P α f negative)
    (radialD_bottom P α f negative)
    (capX_bottom P α f negative)
    (capY_bottom P α f negative)
    (capZ_bottom P α f negative)
    (capW_bottom P α f negative)
    (capV_bottom P α f negative)
    (capU_bottom P α f negative)
    (first_bottom P α f negative)
    (middle_bottom P α f negative)
    (last_bottom P α f negative)
    r s

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingBottom
