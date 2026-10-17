/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialSourceAttachment

/-! The original Q and terminally paused A pieces in the genuine polynomial single sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
open CommonReferenceNerve CoefficientBassRaw1PolynomialSourceAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The unchanged target cone homotopy at the original terminally paused polynomial A path. -/
def last : C(I × I, carrier P β p q) :=
  (cylinder P β p q).comp
    ⟨fun z ↦ (polynomialPausedPath P p q z.1, z.2), by fun_prop⟩

/-- The Q-top and A-bottom join is a whole scalar reference equality. -/
theorem seam (r : I) : chartSquare P β p q (r, 1) = last P β p q (r, 0) := by
  dsimp only [last, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [cylinder_zero]
  change laurent P β p q
    (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 1)) = _
  rw [sheetFamily_right_attaching]

theorem last_one (r : I) : last P β p q (r, 1) = tip P β p q :=
  cylinder_one P β p q (polynomialPausedPath P p q r)

/-- The initial edge of the chart-square half of the polynomial-pair cap. -/
def leftEdge : C(I, carrier P β p q) :=
  ⟨fun r ↦ chartSquare P β p q (r, 0), by fun_prop⟩
/-- The terminal chart-square edge, shared with the initial cylinder edge. -/
def middleEdge : C(I, carrier P β p q) :=
  ⟨fun r ↦ chartSquare P β p q (r, 1), by fun_prop⟩
/-- The constant edge at the polynomial-pair cone tip. -/
def rightEdge : C(I, carrier P β p q) := ContinuousMap.const _ (tip P β p q)

/-- The chart-square homotopy from the initial edge to the shared middle edge. -/
def firstSwap : (leftEdge P β p q).Homotopy (middleEdge P β p q) where
  toFun z := chartSquare P β p q (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The cylinder homotopy from the shared middle edge to the constant tip edge. -/
def lastSwap : (middleEdge P β p q).Homotopy (rightEdge P β p q) where
  toFun z := last P β p q (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (seam P β p q r).symm
  map_one_left r := last_one P β p q r

/-- The original outer-height half split, before its prescribed reassociation correction. -/
def initial : C(I × I, carrier P β p q) :=
  ⟨fun z ↦ ((firstSwap P β p q).trans (lastSwap P β p q)) (z.2, z.1), by fun_prop⟩

theorem initial_left (r : I) : initial P β p q (r, 0) = chartSquare P β p q (r, 0) :=
  ((firstSwap P β p q).trans (lastSwap P β p q)).apply_zero r

theorem initial_right (r : I) : initial P β p q (r, 1) = tip P β p q :=
  ((firstSwap P β p q).trans (lastSwap P β p q)).apply_one r

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
