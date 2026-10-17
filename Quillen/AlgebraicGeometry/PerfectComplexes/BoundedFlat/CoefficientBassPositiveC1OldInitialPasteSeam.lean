/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldChartClockedRail
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldPolynomialCylinderRail
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1InitialMovingNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1ShiftedInitialMovingNull

/-! Both original old-null tail seams, with the exact chart/cylinder half clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1OldInitialPasteSeam
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0PairedNull
open CoefficientBassPositiveC1OldChartClockedRail
open CoefficientBassPositiveC1OldPolynomialCylinderRail
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The ordinary first half is the entire old positive movement, with its own inner clock. -/
theorem first_minus (s : I) :
    CoefficientBassPositiveC1InitialMovingNull.first P (firstArrow d) (secondArrow d) (0, s) =
      positiveMovementMinus P d s := actual_chart_zero P d s

/-- The shifted first half uses the full common-unit reference action on the same old word. -/
theorem first_plus (s : I) :
    CoefficientBassPositiveC1ShiftedInitialMovingNull.first P
      (firstArrow d) (secondArrow d) (0, s) = positiveMovementPlus P d s := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (CommonReferenceProduct.reanchor
      (LaurentUnitReferenceSpecialization.commonUnit P (firstArrow d) (secondArrow d)))
      (CoefficientBassPositiveC1BoundaryLift.chartParameter P
        (firstArrow d) (secondArrow d) (0, s))) = _
  rw [chart_zero]; rfl

/-- The ordinary initial paste has exactly the old movement followed by its old cone path. -/
theorem initial_minus (s : I) :
    CoefficientBassPositiveC1InitialMovingNull.parameter P
      (firstArrow d) (secondArrow d) (0, s) =
      ((positiveMovementMinus P d).trans (oldConeMinus P d)) s := by
  change ((CoefficientBassPositiveC1InitialMovingNull.firstSwap P
    (firstArrow d) (secondArrow d)).trans
      (CoefficientBassPositiveC1InitialMovingNull.lastSwap P
        (firstArrow d) (secondArrow d))) (s, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact first_minus P d _
  · exact minus_cylinder P d _

/-- The shifted initial paste has the same literal halves and retains its distinct plus tip. -/
theorem initial_plus (s : I) :
    CoefficientBassPositiveC1ShiftedInitialMovingNull.parameter P
      (firstArrow d) (secondArrow d) (0, s) =
      ((positiveMovementPlus P d).trans (oldConePlus P d)) s := by
  change ((CoefficientBassPositiveC1ShiftedInitialMovingNull.firstSwap P
    (firstArrow d) (secondArrow d)).trans
      (CoefficientBassPositiveC1ShiftedInitialMovingNull.lastSwap P
        (firstArrow d) (secondArrow d))) (s, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact first_plus P d _
  · exact plus_cylinder P d _

end Quillen.PerfectComplexes.CoefficientBassPositiveC1OldInitialPasteSeam
