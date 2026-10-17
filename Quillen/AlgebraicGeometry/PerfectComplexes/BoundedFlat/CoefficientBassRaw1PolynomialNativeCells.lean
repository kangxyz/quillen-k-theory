/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingTop
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialOrdinaryNativeCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeConeSupport

/-!
# Actual polynomial native cells in the original two-chart Bass cone

The fixed three-cube paste is evaluated on arbitrary genuine polynomial input and
sent through the literal positive or inverse-chart cone inclusion. Both coherence
coordinates, cylinder height, and the independent structure time remain unchanged.
The source chart is independent of the target chart. No additional extension is chosen.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialNativeCells
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialCommonPastingNative
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)
local notation "p₀" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "q₀" => CategoryTheory.NatTrans.app α a
local notation "l" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "lb" => CategoryTheory.Functor.obj (laurentUnderFunctor R) b
local notation "V" => modelOf (boundedFlatPerfectWaldhausen
  (space (op P, CategoryTheory.Functor.obj (polynomialUnderFunctor R) a)))
local notation "B" => mappingCone (boundedFlatCoefficientBassSquareComparison P lb)

private theorem native_top (negative : Bool) (n : ℕ) (t : I × I)
    (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![t.1, t.2, 1], x) =
      (CommonReferenceNerve.CutOpenCarrier.nativeCone
        (BassMWholeNerve.coefficientModel P
          (CategoryTheory.NatTrans.app (chartChoice negative) lb))).point n := by
  rw [nativeFamily_apply, CoefficientBassRaw1PolynomialCommonPastingTop.family_top]
  exact CoefficientBassRaw1PolynomialOrdinaryMap.evaluate_tip P p₀ q₀ l
    (chartChoice negative) n x

/-- The fixed plus polynomial cell enters the original two-chart cone with all clocks intact. -/
def plus (n : ℕ) : C((I × I) × (I × (prespectrum V).space n), (B).space n) :=
  ((boundedFlatCoefficientBassPositiveConeInclusion P lb).map n).comp
    ((nativeFamily P α f false n).comp
      ⟨fun z : (I × I) × (I × (prespectrum V).space n) ↦
        (![z.1.1, z.1.2, z.2.1], z.2.2), by fun_prop⟩)

/-- Exact evaluation uses the selected original paste and literal plus cone inclusion. -/
theorem plus_apply (n : ℕ) (t : I × I) (h : I) (x : (prespectrum V).space n) :
    plus P α f n (t, (h, x)) =
      (boundedFlatCoefficientBassPositiveConeInclusion P lb).map n
        (nativeFamily P α f false n (![t.1, t.2, h], x)) := rfl

/-- The complete plus cell preserves the original polynomial basepoint. -/
theorem plus_point (n : ℕ) (t : I × I) (h : I) :
    plus P α f n (t, (h, (prespectrum V).point n)) = (B).point n := by
  rw [plus_apply, nativeFamily_point]
  exact (boundedFlatCoefficientBassPositiveConeInclusion P lb).map_point n

/-- Structure time is independent of both coherence coordinates and the plus cylinder height. -/
theorem plus_structure (n : ℕ) (t : I × I) (h : I)
    (x : (prespectrum V).space n) (s : I) :
    plus P α f (n + 1) (t, (h, (prespectrum V).structureMap n x s)) =
      (B).structureMap n (plus P α f n (t, (h, x))) s := by
  rw [plus_apply, nativeFamily_structure, plus_apply]
  exact congrArg (fun γ ↦ γ s)
    ((boundedFlatCoefficientBassPositiveConeInclusion P lb).comm n
      (nativeFamily P α f false n (![t.1, t.2, h], x)))

/-- The whole height-one face of the plus cell is the original two-chart cone point. -/
theorem plus_top (n : ℕ) (t : I × I) (x : (prespectrum V).space n) :
    plus P α f n (t, (1, x)) = (B).point n := by
  rw [plus_apply, native_top]
  exact (boundedFlatCoefficientBassPositiveConeInclusion P lb).map_point n

/-- The fixed minus polynomial cell enters the original two-chart cone with all clocks intact. -/
def minus (n : ℕ) : C((I × I) × (I × (prespectrum V).space n), (B).space n) :=
  ((boundedFlatCoefficientBassNegativeConeInclusion P lb).map n).comp
    ((nativeFamily P α f true n).comp
      ⟨fun z : (I × I) × (I × (prespectrum V).space n) ↦
        (![z.1.1, z.1.2, z.2.1], z.2.2), by fun_prop⟩)

/-- Exact evaluation uses the selected original paste and literal minus cone inclusion. -/
theorem minus_apply (n : ℕ) (t : I × I) (h : I) (x : (prespectrum V).space n) :
    minus P α f n (t, (h, x)) =
      (boundedFlatCoefficientBassNegativeConeInclusion P lb).map n
        (nativeFamily P α f true n (![t.1, t.2, h], x)) := rfl

/-- The complete minus cell preserves the original polynomial basepoint. -/
theorem minus_point (n : ℕ) (t : I × I) (h : I) :
    minus P α f n (t, (h, (prespectrum V).point n)) = (B).point n := by
  rw [minus_apply, nativeFamily_point]
  exact (boundedFlatCoefficientBassNegativeConeInclusion P lb).map_point n

/-- Structure time is independent of both coherence coordinates and the minus cylinder height. -/
theorem minus_structure (n : ℕ) (t : I × I) (h : I)
    (x : (prespectrum V).space n) (s : I) :
    minus P α f (n + 1) (t, (h, (prespectrum V).structureMap n x s)) =
      (B).structureMap n (minus P α f n (t, (h, x))) s := by
  rw [minus_apply, nativeFamily_structure, minus_apply]
  exact congrArg (fun γ ↦ γ s)
    ((boundedFlatCoefficientBassNegativeConeInclusion P lb).comm n
      (nativeFamily P α f true n (![t.1, t.2, h], x)))

/-- The whole height-one face of the minus cell is the original two-chart cone point. -/
theorem minus_top (n : ℕ) (t : I × I) (x : (prespectrum V).space n) :
    minus P α f n (t, (1, x)) = (B).point n := by
  rw [minus_apply, native_top]
  exact (boundedFlatCoefficientBassNegativeConeInclusion P lb).map_point n

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialNativeCells
