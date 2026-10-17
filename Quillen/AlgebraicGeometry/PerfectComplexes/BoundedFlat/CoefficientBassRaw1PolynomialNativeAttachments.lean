/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialNativeLower

/-! Both complete polynomial height-zero faces attach to the actual Laurent family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialNativeCells
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)
local notation "V" => modelOf (boundedFlatPerfectWaldhausen
  (space (op P, CategoryTheory.Functor.obj (polynomialUnderFunctor R) a)))
local notation "lb" => CategoryTheory.Functor.obj (laurentUnderFunctor R) b

/-- The entire plus polynomial base face retains the original chart-precomposed input. -/
theorem plus_zero (n : ℕ) (z : I × I) (x : (prespectrum V).space n) :
    plus P α f n (z, (0, x)) =
      CoefficientBassRaw1LaurentNativeCell.family P α f n
        (z, (prespectrumMap (CoefficientBassRaw1LaurentChartRestriction.chart
          P (underToLaurent R) (a := a))).map n x) := by
  rw [plus_apply, CoefficientBassRaw1PolynomialCommonPastingNative.nativeFamily_apply,
    CoefficientBassRaw1PolynomialCommonPasting.family_bottom_restricted]
  exact congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P lb).map n)
    (CoefficientBassRaw1PolynomialNativeLower.lower_native P α (underToLaurent R) f n z x)

/-- The entire minus polynomial base face retains the original chart-precomposed input. -/
theorem minus_zero (n : ℕ) (z : I × I) (x : (prespectrum V).space n) :
    minus P α f n (z, (0, x)) =
      CoefficientBassRaw1LaurentNativeCell.family P α f n
        (z, (prespectrumMap (CoefficientBassRaw1LaurentChartRestriction.chart
          P (underToLaurentInvert R) (a := a))).map n x) := by
  rw [minus_apply, CoefficientBassRaw1PolynomialCommonPastingNative.nativeFamily_apply,
    CoefficientBassRaw1PolynomialCommonPasting.family_bottom_restricted]
  exact congrArg ((boundedFlatCoefficientBassNegativeConeInclusion P lb).map n)
    (CoefficientBassRaw1PolynomialNativeLower.lower_native P α (underToLaurentInvert R) f n z x)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialNativeCells
