/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingBottom

/-! The entire prescribed Laurent family is retained under its actual source-chart reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPasting
open CommonReferenceNerve CoefficientBassRaw1PolynomialTripleRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b) (negative : Bool)

/-- The whole bottom is the old Laurent18 family restricted on genuine polynomial inputs. -/
theorem family_bottom_restricted (r s : I) :
    family P α f negative ![r, s, 0] =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α (chartChoice negative) f
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialReference.referenceIso
          P α (chartChoice negative) f).symm)
        (CoefficientBassRaw1LaurentChartRestriction.family
          P α (chartChoice negative) f (r, s))) := by
  rw [CoefficientBassRaw1PolynomialCommonPastingBottom.family_bottom,
    CoefficientBassRaw1LaurentChartRestriction.family_parameter]
  have he := mapParameter_parameter
    (CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialReference.referenceIso
      P α (chartChoice negative) f).symm)
    (CoefficientBassRaw1LaurentChartRestriction.nodes P α (chartChoice negative) f)
    (CoefficientBassLaurentProjectionScalar.scalarComparison (r, s))
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent
    P α (chartChoice negative) f) he.symm

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPasting
