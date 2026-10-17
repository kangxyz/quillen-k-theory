/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0PairedNullNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0PositiveRailsNative

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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0FullNullNative
open CommonReferenceNerve CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0PairedNull
open CoefficientBassCompositeJ0RectangleNative CoefficientBassCompositeJ0PairedNullNative
open CoefficientBassCompositeJ0PositiveRailsNative
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The minus straightPositive retains every native level, input and original clock. -/
theorem straightPositiveMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (straightPositiveMinus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.straightPositivePasting P (arrow p q)).level n
        (r, (s, x)) := by
  let ev : Carrier P p q → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  unfold straightPositiveMinus CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.straightPositiveWord n x ev
    (oldPositiveMinus P p q)
    (positiveMovementMinus P p q)
    (polynomialMovementMinus P p q)
    (laurentMovementMinus P p q)
    (newPositiveMinus P p q)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow p q))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow p q))
    (rectangleMinus P p q)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow p q))
    (fun t ↦ oldPositiveMinus_native P p q n t x)
    (fun t ↦ positiveMovementMinus_native P p q n t x)
    (fun t ↦ polynomialMovementMinus_native P p q n t x)
    (fun t ↦ laurentMovementMinus_native P p q n t x)
    (fun t ↦ newPositiveMinus_native P p q n t x)
    (fun a b ↦ rectangleMinus_positivePasting P p q n a b x)
    r s

/-- The minus pastedNull retains every native level, input and original clock. -/
theorem pastedNullMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (pastedNullMinus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.pastedNullComparison P (arrow p q)).level n
        (r, (s, x)) := by
  let ev : Carrier P p q → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  unfold pastedNullMinus CoefficientBassPositiveNullTrack.pastedNullComparison
  unfold CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.pastedPositiveNullWord n x ev
    (oldPositiveMinus P p q)
    (positiveMovementMinus P p q)
    (polynomialMovementMinus P p q)
    (laurentMovementMinus P p q)
    (newPositiveMinus P p q)
    (oldConeMinus P p q)
    (newConeMinus P p q)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow p q))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow p q))
    (CoefficientBassPositiveNullTrack.oldCone P (arrow p q))
    (CoefficientBassPositiveNullTrack.newCone P (arrow p q))
    (rectangleMinus P p q)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow p q))
    (coneComparisonMinus P p q)
    (CoefficientBassPositiveNullTrack.conePasting P (arrow p q))
    (fun t ↦ oldPositiveMinus_native P p q n t x)
    (fun t ↦ positiveMovementMinus_native P p q n t x)
    (fun t ↦ polynomialMovementMinus_native P p q n t x)
    (fun t ↦ laurentMovementMinus_native P p q n t x)
    (fun t ↦ newPositiveMinus_native P p q n t x)
    (fun t ↦ oldConeMinus_native P p q n t x)
    (fun t ↦ newConeMinus_native P p q n t x)
    (fun a b ↦ rectangleMinus_positivePasting P p q n a b x)
    (fun a b ↦ coneComparisonMinus_native P p q n a b x)
    r s

/-- The minus originalNull retains every native level, input and original clock. -/
theorem originalNullMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (pastedNullMinus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow p q)).level n
        (r, (s, x)) := by
  rw [originalNullComparison_apply]
  exact pastedNullMinus_native P p q n r s x

/-- The plus straightPositive retains every native level, input and original clock. -/
theorem straightPositivePlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (straightPositivePlus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.straightPositivePasting P (arrow p q)).level n
        (r, (s, x)) := by
  let ev : Carrier P p q → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  unfold straightPositivePlus CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.straightPositiveWord n x ev
    (oldPositivePlus P p q)
    (positiveMovementPlus P p q)
    (polynomialMovementPlus P p q)
    (laurentMovementPlus P p q)
    (newPositivePlus P p q)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow p q))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow p q))
    (rectanglePlus P p q)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow p q))
    (fun t ↦ oldPositivePlus_native P p q n t x)
    (fun t ↦ positiveMovementPlus_native P p q n t x)
    (fun t ↦ polynomialMovementPlus_native P p q n t x)
    (fun t ↦ laurentMovementPlus_native P p q n t x)
    (fun t ↦ newPositivePlus_native P p q n t x)
    (fun a b ↦ rectanglePlus_positivePasting P p q n a b x)
    r s

/-- The plus pastedNull retains every native level, input and original clock. -/
theorem pastedNullPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (pastedNullPlus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.pastedNullComparison P (arrow p q)).level n
        (r, (s, x)) := by
  let ev : Carrier P p q → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  unfold pastedNullPlus CoefficientBassPositiveNullTrack.pastedNullComparison
  unfold CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.pastedPositiveNullWord n x ev
    (oldPositivePlus P p q)
    (positiveMovementPlus P p q)
    (polynomialMovementPlus P p q)
    (laurentMovementPlus P p q)
    (newPositivePlus P p q)
    (oldConePlus P p q)
    (newConePlus P p q)
    (CoefficientBassPositiveNullTrack.oldPositive P (arrow p q))
    (CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q))
    (CoefficientBassPositiveNullTrack.newPositive P (arrow p q))
    (CoefficientBassPositiveNullTrack.oldCone P (arrow p q))
    (CoefficientBassPositiveNullTrack.newCone P (arrow p q))
    (rectanglePlus P p q)
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow p q))
    (coneComparisonPlus P p q)
    (CoefficientBassPositiveNullTrack.conePasting P (arrow p q))
    (fun t ↦ oldPositivePlus_native P p q n t x)
    (fun t ↦ positiveMovementPlus_native P p q n t x)
    (fun t ↦ polynomialMovementPlus_native P p q n t x)
    (fun t ↦ laurentMovementPlus_native P p q n t x)
    (fun t ↦ newPositivePlus_native P p q n t x)
    (fun t ↦ oldConePlus_native P p q n t x)
    (fun t ↦ newConePlus_native P p q n t x)
    (fun a b ↦ rectanglePlus_positivePasting P p q n a b x)
    (fun a b ↦ coneComparisonPlus_native P p q n a b x)
    r s

/-- The plus originalNull retains every native level, input and original clock. -/
theorem originalNullPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (pastedNullPlus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow p q)).level n
        (r, (s, x)) := by
  rw [originalNullComparison_apply]
  exact pastedNullPlus_native P p q n r s x

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0FullNullNative
