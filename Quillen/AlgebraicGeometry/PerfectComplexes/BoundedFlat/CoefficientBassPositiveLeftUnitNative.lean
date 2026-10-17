/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftUnitPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftNativeFamilies
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftNativePostcomp

/-! Exact native recovery of both transported original unit-pasting surfaces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitNative
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftMidpointUnit
open CoefficientBassPositiveLeftUnitPasting CoefficientBassPositiveLeftNativeFamilies
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The whole first TenNodes pasting retains its original scalar parameter and Laurent q map. -/
theorem first_unit_original_value (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstUnitComparison P p q (r, s)) x =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
        ((boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map q))).map n
          ((boundedFlatCoefficientLaurentUnitPasting P p).level n (r, (s, x)))) := by
  rw [firstUnitComparison_apply]
  change nativeValue P p q n (includeLaurent P p q
    (mapParameter (firstTransport P p q)
      (parameter (CoefficientLaurentUnitTenNodes.source P p)
        (CoefficientLaurentUnitTenNodes.nodes P p)
        (CoefficientLaurentUnitPastingLift.parameter (r, s))))) x = _
  rw [mapParameter_parameter, laurent_parameter_native, first_transport_family,
    prespectrumFamily_eq]
  exact congrArg (fun y ↦
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
      ((boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map q))).map n y))
    (CoefficientLaurentUnitPastingLift.original_lift P p n r s x)

/-- The first full unit comparison is exactly the original p unitPasting followed by cone q. -/
theorem first_unit_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstUnitComparison P p q (r, s)) x =
      (boundedFlatCoefficientBassPositiveConeMap P q).map n
        ((CoefficientBassPositiveTransitionTrack.unitPasting P p).level n (r, (s, x))) := by
  rw [first_unit_original_value, unitPasting_value]
  exact cone_inclusion P q n _

/-- This is also the exact typed native unit input for first two-sheet conjugation. -/
theorem first_unit_postcomp (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstUnitComparison P p q (r, s)) x =
      (CoefficientBassPositiveLeftNativePostcomp.unitPasting P p q).level n (r, (s, x)) :=
  (first_unit_native P p q n r s x).trans
    (CoefficientBassPositiveLeftNativePostcomp.unitPasting_mapped P p q n x r s)

/-- The whole middle TenNodes pasting retains coefficient p on every genuine native input. -/
theorem middle_unit_original_value (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middleUnitComparison P p q (r, s)) x =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
        ((boundedFlatCoefficientLaurentUnitPasting P q).level n
          (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))) := by
  rw [middleUnitComparison_apply]
  change nativeValue P p q n (includeLaurent P p q
    (mapParameter (middleTransport P p q)
      (parameter (CoefficientLaurentUnitTenNodes.source P q)
        (CoefficientLaurentUnitTenNodes.nodes P q)
        (CoefficientLaurentUnitPastingLift.parameter (r, s))))) x = _
  rw [mapParameter_parameter, laurent_parameter_native, middle_transport_family,
    prespectrumFamily_eq]
  exact congrArg
    ((mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n)
    (CoefficientLaurentUnitPastingLift.original_lift P q n r s
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))

/-- The middle full unit comparison is the unchanged q unitPasting at coefficient p of x. -/
theorem middle_unit_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middleUnitComparison P p q (r, s)) x =
      (CoefficientBassPositiveTransitionTrack.unitPasting P q).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  rw [middle_unit_original_value, unitPasting_value]

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitNative
