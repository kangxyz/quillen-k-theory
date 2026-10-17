/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0UnitPasting

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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0C0SeedAlignment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- Both actual constructions use the same complete two-attachment carrier type. -/
theorem carrier_eq :
    CoefficientBassPositiveC0CarrierSeed.Carrier P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) =
      CoefficientBassPositiveJ0Rectangles.Carrier P d := rfl

/-- The carrier alignment is the identity on points, with its original topology. -/
def toJ0 : C(CoefficientBassPositiveC0CarrierSeed.Carrier P
    ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d),
    CoefficientBassPositiveJ0Rectangles.Carrier P d) :=
  ⟨fun z => z, continuous_id⟩

/-- The minus tip is preserved independently of the plus tip. -/
theorem toJ0_minusTip :
    toJ0 P d (CoefficientBassPositiveC0CarrierSeed.minusTip P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)) =
    CommonReferenceNerve.CutOpenCarrier.tipMinus
      (CoefficientBassPositiveJ0ConeBoundaries.polyRef P d)
      (CoefficientBassPositiveJ0ConeBoundaries.chart P d)
      (CoefficientBassPositiveJ0ConeBoundaries.laurentRef P d)
      (CoefficientBassPositiveJ0ConeBoundaries.ordinary P d)
      (CoefficientBassPositiveJ0ConeBoundaries.shifted P d) := rfl

/-- The plus tip is preserved without identifying the two tips. -/
theorem toJ0_plusTip :
    toJ0 P d (CoefficientBassPositiveC0CarrierSeed.plusTip P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)) =
    CommonReferenceNerve.CutOpenCarrier.tipPlus
      (CoefficientBassPositiveJ0ConeBoundaries.polyRef P d)
      (CoefficientBassPositiveJ0ConeBoundaries.chart P d)
      (CoefficientBassPositiveJ0ConeBoundaries.laurentRef P d)
      (CoefficientBassPositiveJ0ConeBoundaries.ordinary P d)
      (CoefficientBassPositiveJ0ConeBoundaries.shifted P d) := rfl

/-- The whole C0 source unit is the actual direct-Laurent new-unit rail, at the same time. -/
theorem source_unit_newUnit (s : I) :
    toJ0 P d (CoefficientBassPositiveC0CarrierSeed.forwardUnit P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) (s, 0)) =
      CoefficientBassPositiveJ0UnitPasting.newUnit P d s := by
  change CoefficientBassPositiveC0CarrierSeed.forwardUnit P
    ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) (s, 0) =
      CoefficientBassPositiveJ0DirectUnit.directUnitMap P d (CoefficientLaurentUnitTenNodes.W s)
  exact CoefficientBassPositiveC0CarrierSeed.actual_source_unit P d s

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0C0SeedAlignment
