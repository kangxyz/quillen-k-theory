/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0UnitPasting

/-!
# The actual C0 and J0 carrier alignment

The polynomial reference, chart, Laurent reference and both attachment isomorphisms agree
literally. The complete direct-Laurent unit rail is identified before assembling null words.
-/
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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0C0SeedAlignment
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Both actual constructions use the same complete two-attachment carrier type. -/
theorem carrier_eq :
    CoefficientBassPositiveC0CarrierSeed.Carrier P
      p q =
      CoefficientBassCompositeJ0Rectangles.Carrier P p q := rfl

/-- The carrier alignment is the identity on points, with its original topology. -/
def toJ0 : C(CoefficientBassPositiveC0CarrierSeed.Carrier P
    p q,
    CoefficientBassCompositeJ0Rectangles.Carrier P p q) :=
  ⟨fun z => z, continuous_id⟩

/-- The minus tip is preserved independently of the plus tip. -/
theorem toJ0_minusTip :
    toJ0 P p q (CoefficientBassPositiveC0CarrierSeed.minusTip P
      p q) =
    CommonReferenceNerve.CutOpenCarrier.tipMinus
      (CoefficientBassCompositeJ0ConeBoundaries.polyRef P p q)
      (CoefficientBassCompositeJ0ConeBoundaries.chart P (c := c))
      (CoefficientBassCompositeJ0ConeBoundaries.laurentRef P p q)
      (CoefficientBassCompositeJ0ConeBoundaries.ordinary P p q)
      (CoefficientBassCompositeJ0ConeBoundaries.shifted P p q) := rfl

/-- The plus tip is preserved without identifying the two tips. -/
theorem toJ0_plusTip :
    toJ0 P p q (CoefficientBassPositiveC0CarrierSeed.plusTip P
      p q) =
    CommonReferenceNerve.CutOpenCarrier.tipPlus
      (CoefficientBassCompositeJ0ConeBoundaries.polyRef P p q)
      (CoefficientBassCompositeJ0ConeBoundaries.chart P (c := c))
      (CoefficientBassCompositeJ0ConeBoundaries.laurentRef P p q)
      (CoefficientBassCompositeJ0ConeBoundaries.ordinary P p q)
      (CoefficientBassCompositeJ0ConeBoundaries.shifted P p q) := rfl

/-- The whole C0 source unit is the actual direct-Laurent new-unit rail, at the same time. -/
theorem source_unit_newUnit (s : I) :
    toJ0 P p q (CoefficientBassPositiveC0CarrierSeed.forwardUnit P
      p q (s, 0)) =
      CoefficientBassCompositeJ0UnitPasting.newUnit P p q s := by
  change CoefficientBassPositiveC0CarrierSeed.forwardUnit P p q (s, 0) =
    CoefficientBassCompositeJ0RectangleRails.unitMap P p q (CoefficientLaurentUnitTenNodes.W s)
  exact CoefficientBassPositiveC0CarrierSeed.source_unit P p q s


end Quillen.PerfectComplexes.CoefficientBassCompositeJ0C0SeedAlignment
