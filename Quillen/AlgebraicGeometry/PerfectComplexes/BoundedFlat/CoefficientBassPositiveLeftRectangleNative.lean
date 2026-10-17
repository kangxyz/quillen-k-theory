/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftRectangles
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftNativeFamilies
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftNativePostcomp
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0Native

/-! Both original finite positive rectangles, at every native level and genuine input. -/
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

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftRectangleNative
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftCellParameters
open CoefficientBassPositiveLeftRectangles CoefficientBassPositiveLeftMidpointUnit
open CoefficientBassPositiveLeftNativeFamilies
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Both first sheets retain the full original p family at every finite simplex point. -/
theorem first_family (e : Bool) (n : ℕ) (z : StdSimplex ℝ (Fin 31))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P p q) (firstRectangleNodes P p q e) n (z, x) =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map q))).map n
          (prespectrumFamily (BassH0Diagram.reference P p) (BassH0Diagram.nodes P p) n (z, x)) := by
  cases e
  · exact first_transport_family P p q (BassH0Diagram.nodes P p) n z x
  · change prespectrumFamily (laurentReference P p q)
      (ModelSimplex.reanchorNodes (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (BassH1References.firstNodes P p q)) n (z, x) = _
    rw [prespectrumFamily_reanchor]
    exact first_transport_family P p q (BassH0Diagram.nodes P p) n z x

/-- Both middle sheets retain the full q family at the actual coefficient-p input. -/
theorem middle_family (e : Bool) (n : ℕ) (z : StdSimplex ℝ (Fin 31))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P p q) (middleRectangleNodes P p q e) n (z, x) =
      prespectrumFamily (BassH0Diagram.reference P q) (BassH0Diagram.nodes P q) n
        (z, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x) := by
  cases e
  · exact middle_transport_family P p q (BassH0Diagram.nodes P q) n z x
  · change prespectrumFamily (laurentReference P p q)
      (ModelSimplex.reanchorNodes (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (BassH1References.middleNodes P p q)) n (z, x) = _
    rw [prespectrumFamily_reanchor]
    exact middle_transport_family P p q (BassH0Diagram.nodes P q) n z x

/-- The entire first rectangle retains the original p positive pasting and Laurent q map. -/
theorem first_rectangle_original_value (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstRectangle P p q e (r, s)) x =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
        ((boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map q))).map n
          ((boundedFlatCoefficientPlusPasting P p).level n (r, (s, x)))) := by
  rw [first_rectangle_apply]
  change nativeValue P p q n (includeLaurent P p q
    (parameter (laurentReference P p q) (firstRectangleNodes P p q e)
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)))) x = _
  rw [laurent_parameter_native, first_family, prespectrumFamily_eq]
  exact congrArg (fun y ↦
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
      ((boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map q))).map n y))
    (BassH0Diagram.plus_rectangle_lift P p n r s x)

/-- The first rectangle is exactly the original p positivePasting postcomposed by cone q. -/
theorem first_rectangle_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstRectangle P p q e (r, s)) x =
      (boundedFlatCoefficientBassPositiveConeMap P q).map n
        ((CoefficientBassPositiveNullTrack.positivePasting P p).level n (r, (s, x))) := by
  rw [first_rectangle_original_value, positivePasting_value]
  exact cone_inclusion P q n _

/-- The same first value has the precise postcomposed boundary type used by native null words. -/
theorem first_rectangle_postcomp (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstRectangle P p q e (r, s)) x =
      (CoefficientBassPositiveLeftNativePostcomp.positivePasting P p q).level n (r, (s, x)) :=
  (first_rectangle_native P p q e n r s x).trans
    (CoefficientBassPositiveLeftNativePostcomp.positivePasting_mapped P p q n x r s)

/-- The entire middle rectangle is the original q pasting at the actual precomposed input. -/
theorem middle_rectangle_original_value (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middleRectangle P p q e (r, s)) x =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
        ((boundedFlatCoefficientPlusPasting P q).level n
          (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))) := by
  rw [middle_rectangle_apply]
  change nativeValue P p q n (includeLaurent P p q
    (parameter (laurentReference P p q) (middleRectangleNodes P p q e)
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)))) x = _
  rw [laurent_parameter_native, middle_family, prespectrumFamily_eq]
  exact congrArg
    ((mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n)
    (BassH0Diagram.plus_rectangle_lift P q n r s
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))

/-- The middle rectangle retains the original q positivePasting, including all boundary casts. -/
theorem middle_rectangle_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middleRectangle P p q e (r, s)) x =
      (CoefficientBassPositiveNullTrack.positivePasting P q).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  rw [middle_rectangle_original_value, positivePasting_value]

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftRectangleNative
