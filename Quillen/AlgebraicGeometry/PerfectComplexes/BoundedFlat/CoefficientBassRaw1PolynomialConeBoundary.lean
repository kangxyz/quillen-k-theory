/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialReference
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! The fixed whole Laurent comparison enters the actual polynomial sheet by its full anchor. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCone
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The direction transports the fixed chart-restricted reference into the actual sheet. -/
def boundaryAnchor : (laurentReference P α β f).functor ≅
    (CoefficientBassRaw1PolynomialReference.reference P α β f).functor :=
  (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm

/-- All eighteen complete references are carried through the actual normalization isomorphism. -/
def boundaryNodes := fun i : Fin 18 ↦
  CommonReferenceProduct.reanchor (boundaryAnchor P α β f)
    (CoefficientBassRaw1LaurentChartRestriction.nodes P α β f i)

/-- The prescribed Laurent T-family keeps every interior point and both original clocks. -/
def boundaryFamily : C(I × I, |parameterSSet (laurentReference P α β f)|) :=
  (mapParameter (CommonReferenceProduct.reanchor (boundaryAnchor P α β f))).comp
    (CoefficientBassRaw1LaurentChartRestriction.family P α β f)

/-- This is equality of complete scalar nerve parameters, before native evaluation. -/
theorem boundaryFamily_parameter (z : I × I) : boundaryFamily P α β f z =
    parameter (laurentReference P α β f) (boundaryNodes P α β f)
      (CoefficientBassLaurentProjectionScalar.scalarComparison z) := by
  change mapParameter (CommonReferenceProduct.reanchor (boundaryAnchor P α β f))
    (CoefficientBassRaw1LaurentChartRestriction.family P α β f z) = _
  rw [CoefficientBassRaw1LaurentChartRestriction.family_parameter, mapParameter_parameter]
  rfl

/-- The whole fixed Laurent face sits in the literal Laurent summand of the single sheet. -/
def fixedLaurentFace : C(I × I, space P α β f) :=
  (laurent P α β f).comp (boundaryFamily P α β f)

/-- The whole face has its exact all-degree value on every genuine polynomial input. -/
theorem fixedLaurentFace_native (n : ℕ) (z : I × I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space
        (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P α β f n (fixedLaurentFace P α β f z) x =
      (Quillen.LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P β (b := b)))).map n
        (pointwisePrespectrumFamily (CoefficientBassLaurentProjectionScalar.reference P α f)
          n (CoefficientBassLaurentProjectionScalar.family P α f z)
          ((boundedFlatPerfectPrespectrumMap (coefficientMap P (β.app a))).map n x)) := by
  have h := evaluate_laurent P α β f n (boundaryFamily P α β f z) x
  have hr := pointwise_reanchor (boundaryAnchor P α β f) n
    (CoefficientBassRaw1LaurentChartRestriction.family P α β f z) x
  have hp := CoefficientBassRaw1LaurentChartRestriction.family_native P α β f n z x
  exact h.trans (congrArg
    ((Quillen.LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P β (b := b)))).map n)
    (hr.trans hp))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCone
