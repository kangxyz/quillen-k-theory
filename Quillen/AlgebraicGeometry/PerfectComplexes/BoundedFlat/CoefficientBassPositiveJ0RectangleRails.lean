/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0Rectangles
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0ShiftedBridge

/-!
# Exact outer TenNodes rails and separate positive-rail endpoint joins

Only the Laurent outer word is a whole TenNodes rail. The old and new positive binary paths
retain their chart vertices and meet that word at their Laurent endpoints.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0RectangleRails
open CommonReferenceNerve BassH0Merge CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The original composite-arrow TenNodes simplex with the actual common-reference anchor. -/
def unitMap : C(StdSimplex ℝ (Fin 10), Carrier P d) :=
  (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d)).comp
    ((mapParameter (anchorNode (eqToIso
      (BassH0Merge.reference_eq P (firstArrow d) (secondArrow d))))).comp
      (parameter (CoefficientLaurentUnitTenNodes.source P ((firstArrow d) ≫ (secondArrow d)))
        (CoefficientLaurentUnitTenNodes.nodes P ((firstArrow d) ≫ (secondArrow d)))))

/-- The ordinary entire outer word is the original lower TenNodes boundary word. -/
theorem outerMinus (s : I) :
    laurentMovementMinus P d s = unitMap P d
      ((CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0) s) := by
  have h := CoefficientBassPositiveJ0OuterBridge.anchored_outer_parameter
    P (firstArrow d) (secondArrow d) s
  rw [mapParameter_parameter] at h
  exact congrArg (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d)
    (laurentRef P d) (ordinary P d) (shifted P d)) h

/-- The shifted entire outer word is the original upper TenNodes boundary word. -/
theorem outerPlus (s : I) :
    laurentMovementPlus P d s = unitMap P d
      ((CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1) s) := by
  have h := CoefficientBassPositiveJ0ShiftedBridge.anchored_shifted_parameter
    P (firstArrow d) (secondArrow d) ((firstArrow d) ≫ (secondArrow d))
    (eqToIso (BassH0Merge.reference_eq P (firstArrow d) (secondArrow d))) s
  rw [mapParameter_parameter] at h
  exact congrArg (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d)
    (laurentRef P d) (ordinary P d) (shifted P d)) h

/-- The minus old outer join retains its original full-node endpoint. -/
theorem old_outer_minus :
    oldPositiveMinus P d 0 = laurentMovementMinus P d 0 :=
  (oldPositiveMinus P d).source.trans (laurentMovementMinus P d).source.symm

/-- The minus old chart join retains its original full-node endpoint. -/
theorem old_chart_minus :
    oldPositiveMinus P d 1 = positiveMovementMinus P d 0 :=
  (oldPositiveMinus P d).target.trans (positiveMovementMinus P d).source.symm

/-- The minus new outer join retains its original full-node endpoint. -/
theorem new_outer_minus :
    newPositiveMinus P d 0 = laurentMovementMinus P d 1 :=
  (newPositiveMinus P d).source.trans (laurentMovementMinus P d).target.symm

/-- The minus new chart join retains its original full-node endpoint. -/
theorem new_chart_minus :
    newPositiveMinus P d 1 = polynomialMovementMinus P d 1 :=
  (newPositiveMinus P d).target.trans (polynomialMovementMinus P d).target.symm

/-- The plus old outer join retains its original full-node endpoint. -/
theorem old_outer_plus :
    oldPositivePlus P d 0 = laurentMovementPlus P d 0 :=
  (oldPositivePlus P d).source.trans (laurentMovementPlus P d).source.symm

/-- The plus old chart join retains its original full-node endpoint. -/
theorem old_chart_plus :
    oldPositivePlus P d 1 = positiveMovementPlus P d 0 :=
  (oldPositivePlus P d).target.trans (positiveMovementPlus P d).source.symm

/-- The plus new outer join retains its original full-node endpoint. -/
theorem new_outer_plus :
    newPositivePlus P d 0 = laurentMovementPlus P d 1 :=
  (newPositivePlus P d).source.trans (laurentMovementPlus P d).target.symm

/-- The plus new chart join retains its original full-node endpoint. -/
theorem new_chart_plus :
    newPositivePlus P d 1 = polynomialMovementPlus P d 1 :=
  (newPositivePlus P d).target.trans (polynomialMovementPlus P d).target.symm

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0RectangleRails
