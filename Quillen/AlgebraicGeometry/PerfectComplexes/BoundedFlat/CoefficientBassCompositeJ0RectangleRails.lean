/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Rectangles
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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0RectangleRails
open CommonReferenceNerve BassH0Merge CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original composite-arrow TenNodes simplex with the actual common-reference anchor. -/
def unitMap : C(StdSimplex ℝ (Fin 10), Carrier P p q) :=
  (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q)).comp
    ((mapParameter (anchorNode (eqToIso
      (BassH0Merge.reference_eq P p q)))).comp
      (parameter (CoefficientLaurentUnitTenNodes.source P (p ≫ q))
        (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q))))

/-- The ordinary entire outer word is the original lower TenNodes boundary word. -/
theorem outerMinus (s : I) :
    laurentMovementMinus P p q s = unitMap P p q
      ((CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0) s) := by
  have h := CoefficientBassPositiveJ0OuterBridge.anchored_outer_parameter
    P p q s
  rw [mapParameter_parameter] at h
  exact congrArg (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c))
    (laurentRef P p q) (ordinary P p q) (shifted P p q)) h

/-- The shifted entire outer word is the original upper TenNodes boundary word. -/
theorem outerPlus (s : I) :
    laurentMovementPlus P p q s = unitMap P p q
      ((CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1) s) := by
  have h := CoefficientBassPositiveJ0ShiftedBridge.anchored_shifted_parameter
    P p q (p ≫ q)
    (eqToIso (BassH0Merge.reference_eq P p q)) s
  rw [mapParameter_parameter] at h
  exact congrArg (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c))
    (laurentRef P p q) (ordinary P p q) (shifted P p q)) h

/-- The minus old outer join retains its original full-node endpoint. -/
theorem old_outer_minus :
    oldPositiveMinus P p q 0 = laurentMovementMinus P p q 0 :=
  (oldPositiveMinus P p q).source.trans (laurentMovementMinus P p q).source.symm

/-- The minus old chart join retains its original full-node endpoint. -/
theorem old_chart_minus :
    oldPositiveMinus P p q 1 = positiveMovementMinus P p q 0 :=
  (oldPositiveMinus P p q).target.trans (positiveMovementMinus P p q).source.symm

/-- The minus new outer join retains its original full-node endpoint. -/
theorem new_outer_minus :
    newPositiveMinus P p q 0 = laurentMovementMinus P p q 1 :=
  (newPositiveMinus P p q).source.trans (laurentMovementMinus P p q).target.symm

/-- The minus new chart join retains its original full-node endpoint. -/
theorem new_chart_minus :
    newPositiveMinus P p q 1 = polynomialMovementMinus P p q 1 :=
  (newPositiveMinus P p q).target.trans (polynomialMovementMinus P p q).target.symm

/-- The plus old outer join retains its original full-node endpoint. -/
theorem old_outer_plus :
    oldPositivePlus P p q 0 = laurentMovementPlus P p q 0 :=
  (oldPositivePlus P p q).source.trans (laurentMovementPlus P p q).source.symm

/-- The plus old chart join retains its original full-node endpoint. -/
theorem old_chart_plus :
    oldPositivePlus P p q 1 = positiveMovementPlus P p q 0 :=
  (oldPositivePlus P p q).target.trans (positiveMovementPlus P p q).source.symm

/-- The plus new outer join retains its original full-node endpoint. -/
theorem new_outer_plus :
    newPositivePlus P p q 0 = laurentMovementPlus P p q 1 :=
  (newPositivePlus P p q).source.trans (laurentMovementPlus P p q).target.symm

/-- The plus new chart join retains its original full-node endpoint. -/
theorem new_chart_plus :
    newPositivePlus P p q 1 = polynomialMovementPlus P p q 1 :=
  (newPositivePlus P p q).target.trans (polynomialMovementPlus P p q).target.symm

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0RectangleRails
