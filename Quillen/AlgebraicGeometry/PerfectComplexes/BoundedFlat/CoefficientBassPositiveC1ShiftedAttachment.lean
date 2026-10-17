/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1BoundaryLift

/-! The shifted whole chart attachment before the independent moving-null pasting. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1ShiftedAttachment
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The full chart shifted by the specified common-unit reference, with unchanged coordinates. -/
def shiftedChart : C(I × I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (mapParameter (CommonReferenceProduct.reanchor
    (LaurentUnitReferenceSpecialization.commonUnit P p q))).comp (chartParameter P p q)

/-- The complete right edge is the prescribed shifted polynomial attachment. -/
theorem shiftedChart_right (r : I) : shiftedChart P p q (r, 1) =
    mapParameter (attachPostcompNode (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q))
        (polynomialParameter P p q r) := by
  change mapParameter (CommonReferenceProduct.reanchor
    (LaurentUnitReferenceSpecialization.commonUnit P p q)) (chartParameter P p q (r, 1)) = _
  rw [chart_right_attach]
  exact reanchor_attach_parameter _ _ _ _ _ _

/-- Every shifted chart boundary point meets the plus cylinder at its actual attachment. -/
theorem shiftedChart_seam (r : I) :
    includeLaurent P p q (shiftedChart P p q (r, 1)) =
      plusCylinder P p q (polynomialParameter P p q r, 0) := by
  rw [shiftedChart_right]
  exact (CutOpenCarrier.cylinderPlus_zero _ _ _ _ _ _).symm

/-- Whole native chart evaluation is unchanged by the proved full-reference action. -/
theorem shiftedChart_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    pointwisePrespectrumFamily (laurentReference P p q) n (shiftedChart P p q (r, s)) x =
      pointwisePrespectrumFamily (laurentReference P p q) n (chartParameter P p q (r, s)) x :=
  pointwise_reanchor _ n _ x

end Quillen.PerfectComplexes.CoefficientBassPositiveC1ShiftedAttachment
