/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialNativeCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1LaurentNativeCell
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingLaurentFace
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompNative
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Actual polynomial height-zero families retain the entire original Laurent summand. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialNativeLower
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)
local notation "p₀" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "q₀" => CategoryTheory.NatTrans.app α a
local notation "l" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "lb" => CategoryTheory.Functor.obj (laurentUnderFunctor R) b
local notation "V" => modelOf (boundedFlatPerfectWaldhausen
  (space (op P, CategoryTheory.Functor.obj (polynomialUnderFunctor R) a)))
local notation "J" => BassMWholeNerve.coefficientModel P (CategoryTheory.NatTrans.app β lb)
local notation "A" => CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a)
local notation "F" => CoefficientBassLaurentProjectionScalar.reference P α f

/-- The complete lower reference route recovers arbitrary chart-precomposed native inputs. -/
theorem lower_native (n : ℕ) (z : I × I) (x : (prespectrum V).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P p₀ q₀ l β n
      (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (mapParameter (CommonReferenceProduct.reanchor
          (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm)
          (CoefficientBassRaw1LaurentChartRestriction.family P α β f z))) x =
      (mappingConeInclusion (prespectrumMap J)).map n
        (compactPrespectrumFamily F (CoefficientBassLaurentProjectionScalar.family P α f)
          n (z, (prespectrumMap A).map n x)) := by
  have he := CoefficientBassRaw1PolynomialOrdinaryMap.evaluate_laurent P p₀ q₀ l β n
    (mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm)
      (CoefficientBassRaw1LaurentChartRestriction.family P α β f z)) x
  have hr := pointwise_reanchor
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm n
    (CoefficientBassRaw1LaurentChartRestriction.family P α β f z) x
  have hp := CutOpenPrecomp.pointwise_precomp A F n
    (CoefficientBassLaurentProjectionScalar.family P α f z) x
  have hc := pointwisePrespectrumFamily_eq_compact F
    (CoefficientBassLaurentProjectionScalar.family P α f) n z ((prespectrumMap A).map n x)
  exact he.trans (congrArg ((mappingConeInclusion (prespectrumMap J)).map n)
    (hr.trans (hp.trans hc)))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialNativeLower
