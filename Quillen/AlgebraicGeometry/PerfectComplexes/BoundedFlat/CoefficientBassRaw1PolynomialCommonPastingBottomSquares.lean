/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleCommonBottom

/-! The three actual selected cube bottoms preserve their entire old Laurent squares. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingBottomSquares
open CommonReferenceNerve CoefficientBassRaw1PolynomialTripleRoutes
open CoefficientBassRaw1PolynomialTripleLowerFaces
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b) (negative : Bool)

/-- The continuous full Laurent18 evaluator into the prescribed common polynomial sheet. -/
def bottomMap : C(StdSimplex ℝ (Fin 18),
    CoefficientBassRaw1PolynomialCommonSheet.carrier P α (chartChoice negative) f) :=
  (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α (chartChoice negative) f).comp
    (parameter (targetReference P α (chartChoice negative) f)
      (nodes P α (chartChoice negative) f))

/-- The complete first chosen square has exactly the original bottom parameter. -/
theorem first_bottom (r s : I) :
    CoefficientBassRaw1PolynomialCommonPasting.firstComparison P α f negative (r, s) 0 =
      bottomMap P α f negative (DoubleSquareScalarPaths.firstComparison (r, s)) := by
  exact CoefficientBassRaw1PolynomialTripleCommonBottom.first_extension_bottom
    P α f negative r s

/-- The complete middle chosen square has exactly the original bottom parameter. -/
theorem middle_bottom (r s : I) :
    CoefficientBassRaw1PolynomialCommonPasting.middleComparison P α f negative (r, s) 0 =
      bottomMap P α f negative (DoubleSquareScalarPaths.middleComparison (r, s)) := by
  exact CoefficientBassRaw1PolynomialTripleCommonBottom.middle_extension_bottom
    P α f negative r s

/-- The complete last chosen square has exactly the original bottom parameter. -/
theorem last_bottom (r s : I) :
    CoefficientBassRaw1PolynomialCommonPasting.lastComparison P α f negative (r, s) 0 =
      bottomMap P α f negative (DoubleSquareScalarPaths.lastComparison (r, s)) := by
  exact CoefficientBassRaw1PolynomialTripleCommonBottom.last_extension_bottom
    P α f negative r s

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingBottomSquares
