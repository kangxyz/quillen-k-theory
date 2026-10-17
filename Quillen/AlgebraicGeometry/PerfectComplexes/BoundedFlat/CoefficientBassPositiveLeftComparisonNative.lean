/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftComparisons
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftFullNullNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftUnitRailsNative
public import Quillen.Topology.Prespectrum.RelativeHomotopyTwoSheetConjugationEvaluation

/-!
# Exact recovery of the original Jp and Jq comparisons

The actual finite carrier surfaces recover the original native conjugations at every level,
with genuine degree-zero inputs and independent comparison and output-loop coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftComparisonNative
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftRectangles
open CoefficientBassPositiveLeftPairedNull CoefficientBassPositiveLeftUnitPasting
open CoefficientBassPositiveLeftComparisons CoefficientBassPositiveLeftNativeFamilies
open CoefficientBassPositiveLeftPositiveRailsNative CoefficientBassPositiveLeftFullNullNative
open CoefficientBassPositiveLeftUnitNative CoefficientBassPositiveLeftUnitRailsNative
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete first comparison is the original two-sheet native recipe. -/
theorem first_comparison_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstComparison P p q (r, s)) x =
      (CoefficientBassPositiveLeftNativePostcomp.conjugateComparison P p q).level n
        (r, (s, x)) := by
  let E := originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))
  let T := mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  let ev : Carrier P p q → T.space n := fun z ↦ nativeValue P p q n z x
  exact NativeTwoSheetConjugation.comparison (E := E) (T := T) n
    (x) ev
    (firstOldUnit P p q) (firstNewUnit P p q)
    (firstLaurentMovement P p q false) (firstLaurentMovement P p q true)
    (firstOldNull P p q false) (firstOldNull P p q true)
    (firstNewNull P p q false) (firstNewNull P p q true)
    (CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q)
    (CoefficientBassPositiveLeftNativePostcomp.oldUnit P p q)
    (CoefficientBassPositiveLeftNativePostcomp.newUnit P p q)
    (CoefficientBassPositiveLeftNativePostcomp.originalOldNull P p q)
    (CoefficientBassPositiveLeftNativePostcomp.originalNewNull P p q)
    (firstUnitComparison P p q) (firstPastedNull P p q false)
    (firstPastedNull P p q true)
    (CoefficientBassPositiveLeftNativePostcomp.unitPasting P p q)
    (CoefficientBassPositiveLeftNativePostcomp.originalNullComparison P p q)
    (fun t ↦ first_oldUnit_native P p q n t x)
    (fun t ↦ first_newUnit_native P p q n t x)
    (fun t ↦ first_laurentMovement_native P p q false n t x)
    (fun t ↦ first_laurentMovement_native P p q true n t x)
    (fun t ↦ first_newNull_native P p q false n t x)
    (fun t ↦ first_newNull_native P p q true n t x)
    (fun r s ↦ first_unit_postcomp P p q n r s x)
    (fun r s ↦ first_originalNull_native P p q false n r s x)
    (fun r s ↦ first_originalNull_native P p q true n r s x) r s

/-- The complete middle comparison is the original two-sheet native recipe. -/
theorem middle_comparison_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middleComparison P p q (r, s)) x =
      (CoefficientBassPositiveTransitionTrack.conjugateComparison P q).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let E := originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, b)))
  let T := mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  let ev : Carrier P p q → T.space n := fun z ↦ nativeValue P p q n z x
  exact NativeTwoSheetConjugation.comparison (E := E) (T := T) n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x) ev
    (middleOldUnit P p q) (middleNewUnit P p q)
    (middleLaurentMovement P p q false) (middleLaurentMovement P p q true)
    (middleOldNull P p q false) (middleOldNull P p q true)
    (middleNewNull P p q false) (middleNewNull P p q true)
    (CoefficientBassPositiveNullTrack.laurentMovement P q)
    (CoefficientBassPositiveTransitionTrack.oldUnit P q)
    (CoefficientBassPositiveTransitionTrack.newUnit P q)
    (CoefficientBassPositiveNullTrack.originalOldNull P q)
    (CoefficientBassPositiveNullTrack.originalNewNull P q)
    (middleUnitComparison P p q) (middlePastedNull P p q false)
    (middlePastedNull P p q true)
    (CoefficientBassPositiveTransitionTrack.unitPasting P q)
    (CoefficientBassPositiveNullTrack.originalNullComparison P q)
    (fun t ↦ middle_oldUnit_native P p q n t x)
    (fun t ↦ middle_newUnit_native P p q n t x)
    (fun t ↦ middle_laurentMovement_native P p q false n t x)
    (fun t ↦ middle_laurentMovement_native P p q true n t x)
    (fun t ↦ middle_newNull_native P p q false n t x)
    (fun t ↦ middle_newNull_native P p q true n t x)
    (fun r s ↦ middle_unit_native P p q n r s x)
    (fun r s ↦ middle_originalNull_native P p q false n r s x)
    (fun r s ↦ middle_originalNull_native P p q true n r s x) r s

/-- The first comparison recovers exactly Jp postcomposed by the original cone q map. -/
theorem first_comparison_transition (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstComparison P p q (r, s)) x =
      (boundedFlatCoefficientBassPositiveConeMap P q).map n
        (Path.toContinuousMap
          ((boundedFlatCoefficientBassPositiveTransitionHomotopy P p).level n (r, x)) s) :=
  (first_comparison_native P p q n r s x).trans
    (CoefficientBassPositiveLeftNativePostcomp.conjugateComparison_transition P p q n r s x)

/-- The middle comparison recovers exactly Jq at the original coefficient-p input. -/
theorem middle_comparison_transition (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middleComparison P p q (r, s)) x =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P q).level n
          (r, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s :=
  (middle_comparison_native P p q n r s x).trans
    (boundedFlatCoefficientBassPositiveTransitionHomotopy_apply P q n r s
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftComparisonNative
