/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeC1PolynomialSourceReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldPositiveSourceRails
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldUnitSourceRail
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldChartClockedRail
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFace
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Conjugation

/-! Full original C1 source rails for an arbitrary coefficient-arrow composite. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeC1OldSourceRails
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC1SourceProductStrips CoefficientBassPositiveC1SeedFace
open CoefficientBassCompositeJ0ConeBoundaries CoefficientBassCompositeJ0Rectangles
open CoefficientBassCompositeJ0PairedNull CoefficientBassCompositeJ0TypedUnitRails
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The ordinary product rail retains its whole original clock and complete reference. -/
theorem positive_minus (s : I) : positiveMinus P p q (s, 0) =
    oldPositiveMinus P p q s := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (positiveParameter P p q (0, s)) = _
  rw [CoefficientBassPositiveC1OldPositiveSourceRails.source_parameter]
  rfl

/-- The shifted product rail retains the independent common-unit reference. -/
theorem positive_plus (s : I) : positivePlus P p q (s, 0) =
    oldPositivePlus P p q s := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (CommonReferenceProduct.reanchor
      (LaurentUnitReferenceSpecialization.commonUnit P p q))
      (positiveParameter P p q (0, s))) = _
  rw [CoefficientBassPositiveC1OldPositiveSourceRails.source_parameter]
  rfl

/-- The entire unit source rail uses the original composite-arrow unit parameter. -/
theorem unit (s : I) : forwardUnit P p q (s, 0) = oldUnit P p q s := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _ (unitParameter P p q (0, s)) = _
  rw [CoefficientBassPositiveC1OldUnitSourceRail.source_parameter]
  rfl

/-- The ordinary first half is the whole old chart movement with its literal inner clock. -/
theorem chart_minus (s : I) :
    CoefficientBassPositiveC1InitialMovingNull.first P p q (0, s) =
      positiveMovementMinus P p q s := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _ (chartParameter P p q (0, s)) = _
  rw [CoefficientBassPositiveC1OldChartClockedRail.chart_zero]
  rfl

/-- The shifted chart movement carries the same full common-unit action. -/
theorem chart_plus (s : I) :
    CoefficientBassPositiveC1ShiftedInitialMovingNull.first P p q (0, s) =
      positiveMovementPlus P p q s := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (CommonReferenceProduct.reanchor
      (LaurentUnitReferenceSpecialization.commonUnit P p q))
      (chartParameter P p q (0, s))) = _
  rw [CoefficientBassPositiveC1OldChartClockedRail.chart_zero]
  rfl

/-- Every ordinary cylinder coordinate uses the full polynomial source node. -/
theorem minus_cylinder (s : I) :
    CoefficientBassPositiveC0CarrierSeed.minusCylinder P p q
      (polynomialParameter P p q 0, s) = oldConeMinus P p q s := by
  rw [CoefficientBassCompositeC1PolynomialSourceReference.polynomial_zero]
  rfl

/-- Every shifted cylinder coordinate retains its separate attachment and plus tip. -/
theorem plus_cylinder (s : I) :
    CoefficientBassPositiveC0CarrierSeed.plusCylinder P p q
      (polynomialParameter P p q 0, s) = oldConePlus P p q s := by
  rw [CoefficientBassCompositeC1PolynomialSourceReference.polynomial_zero]
  rfl

end Quillen.PerfectComplexes.CoefficientBassCompositeC1OldSourceRails
