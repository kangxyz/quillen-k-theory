/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PairedNullNative
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PositiveRailsNative

/-!
# Both full original paired-null comparison words

Each sheet retains its own carrier tip, its whole rectangle and cone comparison, and both
independent clocks. The original ofLevels transport is reduced only after the pasted word.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0FullNullNative
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0PairedNull
open CoefficientBassPositiveJ0RectangleNative CoefficientBassPositiveJ0PairedNullNative
open CoefficientBassPositiveJ0PositiveRailsNative
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The minus straightPositive retains every native level, input and original clock. -/
theorem straightPositiveMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (straightPositiveMinus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.straightPositivePasting P (arrow d)).level n
        (r, (s, x)) := by
  let ev : Carrier P d → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  unfold straightPositiveMinus CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.straightPositiveWord n x ev
    (oldPositiveMinus P d)
    (positiveMovementMinus P d)
    (polynomialMovementMinus P d)
    (laurentMovementMinus P d)
    (newPositiveMinus P d)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow d))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow d))
    (rectangleMinus P d)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow d))
    (fun t ↦ oldPositiveMinus_native P d n t x)
    (fun t ↦ positiveMovementMinus_native P d n t x)
    (fun t ↦ polynomialMovementMinus_native P d n t x)
    (fun t ↦ laurentMovementMinus_native P d n t x)
    (fun t ↦ newPositiveMinus_native P d n t x)
    (fun a b ↦ rectangleMinus_positivePasting P d n a b x)
    r s

/-- The minus pastedNull retains every native level, input and original clock. -/
theorem pastedNullMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (pastedNullMinus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.pastedNullComparison P (arrow d)).level n
        (r, (s, x)) := by
  let ev : Carrier P d → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  unfold pastedNullMinus CoefficientBassPositiveNullTrack.pastedNullComparison
  unfold CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.pastedPositiveNullWord n x ev
    (oldPositiveMinus P d)
    (positiveMovementMinus P d)
    (polynomialMovementMinus P d)
    (laurentMovementMinus P d)
    (newPositiveMinus P d)
    (oldConeMinus P d)
    (newConeMinus P d)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow d))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow d))
    (CoefficientBassPositiveNullTrack.oldCone P (arrow d))
    (CoefficientBassPositiveNullTrack.newCone P (arrow d))
    (rectangleMinus P d)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow d))
    (coneComparisonMinus P d)
    (CoefficientBassPositiveNullTrack.conePasting P (arrow d))
    (fun t ↦ oldPositiveMinus_native P d n t x)
    (fun t ↦ positiveMovementMinus_native P d n t x)
    (fun t ↦ polynomialMovementMinus_native P d n t x)
    (fun t ↦ laurentMovementMinus_native P d n t x)
    (fun t ↦ newPositiveMinus_native P d n t x)
    (fun t ↦ oldConeMinus_native P d n t x)
    (fun t ↦ newConeMinus_native P d n t x)
    (fun a b ↦ rectangleMinus_positivePasting P d n a b x)
    (fun a b ↦ coneComparisonMinus_native P d n a b x)
    r s

/-- The minus originalNull retains every native level, input and original clock. -/
theorem originalNullMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (pastedNullMinus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow d)).level n
        (r, (s, x)) := by
  rw [originalNullComparison_apply]
  exact pastedNullMinus_native P d n r s x

/-- The plus straightPositive retains every native level, input and original clock. -/
theorem straightPositivePlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (straightPositivePlus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.straightPositivePasting P (arrow d)).level n
        (r, (s, x)) := by
  let ev : Carrier P d → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  unfold straightPositivePlus CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.straightPositiveWord n x ev
    (oldPositivePlus P d)
    (positiveMovementPlus P d)
    (polynomialMovementPlus P d)
    (laurentMovementPlus P d)
    (newPositivePlus P d)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow d))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow d))
    (rectanglePlus P d)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow d))
    (fun t ↦ oldPositivePlus_native P d n t x)
    (fun t ↦ positiveMovementPlus_native P d n t x)
    (fun t ↦ polynomialMovementPlus_native P d n t x)
    (fun t ↦ laurentMovementPlus_native P d n t x)
    (fun t ↦ newPositivePlus_native P d n t x)
    (fun a b ↦ rectanglePlus_positivePasting P d n a b x)
    r s

/-- The plus pastedNull retains every native level, input and original clock. -/
theorem pastedNullPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (pastedNullPlus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.pastedNullComparison P (arrow d)).level n
        (r, (s, x)) := by
  let ev : Carrier P d → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  unfold pastedNullPlus CoefficientBassPositiveNullTrack.pastedNullComparison
  unfold CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.pastedPositiveNullWord n x ev
    (oldPositivePlus P d)
    (positiveMovementPlus P d)
    (polynomialMovementPlus P d)
    (laurentMovementPlus P d)
    (newPositivePlus P d)
    (oldConePlus P d)
    (newConePlus P d)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow d))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow d))
    (CoefficientBassPositiveNullTrack.oldCone P (arrow d))
    (CoefficientBassPositiveNullTrack.newCone P (arrow d))
    (rectanglePlus P d)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow d))
    (coneComparisonPlus P d)
    (CoefficientBassPositiveNullTrack.conePasting P (arrow d))
    (fun t ↦ oldPositivePlus_native P d n t x)
    (fun t ↦ positiveMovementPlus_native P d n t x)
    (fun t ↦ polynomialMovementPlus_native P d n t x)
    (fun t ↦ laurentMovementPlus_native P d n t x)
    (fun t ↦ newPositivePlus_native P d n t x)
    (fun t ↦ oldConePlus_native P d n t x)
    (fun t ↦ newConePlus_native P d n t x)
    (fun a b ↦ rectanglePlus_positivePasting P d n a b x)
    (fun a b ↦ coneComparisonPlus_native P d n a b x)
    r s

/-- The plus originalNull retains every native level, input and original clock. -/
theorem originalNullPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (pastedNullPlus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow d)).level n
        (r, (s, x)) := by
  rw [originalNullComparison_apply]
  exact pastedNullPlus_native P d n r s x

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0FullNullNative
