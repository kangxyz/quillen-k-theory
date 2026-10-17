/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopyTwoSheetConjugationEvaluation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0TypedUnitRails

/-! The actual two-sheet conjugation and its original native transition image. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0Conjugation
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0PairedNull
open CoefficientBassPositiveJ0TypedUnitRails CoefficientBassPositiveJ0FullNullNative
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The complete old conjugate word joins the two distinct carrier tips. -/
abbrev sourceWord := (oldNullMinus P d).symm.trans ((oldUnit P d).trans (oldNullPlus P d))

/-- The complete new conjugate word retains the same two distinct carrier tips. -/
abbrev targetWord := (newNullMinus P d).symm.trans ((newUnit P d).trans (newNullPlus P d))

/-- The literal original conjugation is assembled from actual whole unit and null comparisons. -/
def comparison : (sourceWord P d).Homotopy (targetWord P d) :=
  Path.Homotopy.TwoSheetConjugation.comparison (oldUnit P d) (newUnit P d)
    (laurentMovementMinus P d) (laurentMovementPlus P d)
    (oldNullMinus P d) (oldNullPlus P d) (newNullMinus P d) (newNullPlus P d)
    (unitComparison P d) (pastedNullMinus P d) (pastedNullPlus P d)

/-- Every level, input and independent pair of times has the original conjugateComparison image. -/
theorem comparison_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (comparison P d (r, s)) x =
      (CoefficientBassPositiveTransitionTrack.conjugateComparison P (arrow d)).level n
        (r, (s, x)) := by
  let E := originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))
  let F := LoopPrespectrum.mappingCone
    (boundedFlatPerfectPrespectrumMap (laurentPlus P ((laurentUnderFunctor R).obj d)))
  let ev : Carrier P d → F.space n := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  exact NativeTwoSheetConjugation.comparison (E := E) (T := F) n x ev
    (oldUnit P d) (newUnit P d) (laurentMovementMinus P d) (laurentMovementPlus P d)
    (oldNullMinus P d) (oldNullPlus P d) (newNullMinus P d) (newNullPlus P d)
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d))
    (CoefficientBassPositiveTransitionTrack.oldUnit P (arrow d))
    (CoefficientBassPositiveTransitionTrack.newUnit P (arrow d))
    (CoefficientBassPositiveNullTrack.originalOldNull P (arrow d))
    (CoefficientBassPositiveNullTrack.originalNewNull P (arrow d))
    (unitComparison P d) (pastedNullMinus P d) (pastedNullPlus P d)
    (CoefficientBassPositiveTransitionTrack.unitPasting P (arrow d))
    (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow d))
    (fun t ↦ oldUnit_native P d n t x) (fun t ↦ newUnit_native P d n t x)
    (fun t ↦ movementMinus_native P d n t x) (fun t ↦ movementPlus_native P d n t x)
    (fun t ↦ newNullMinus_native P d n t x) (fun t ↦ newNullPlus_native P d n t x)
    (fun a b ↦ unitComparison_native P d n a b x)
    (fun a b ↦ originalNullMinus_native P d n a b x)
    (fun a b ↦ originalNullPlus_native P d n a b x) r s

/-- Original zero-loop-map and endpoint casts retain this complete native comparison. -/
theorem comparison_transition (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (comparison P d (r, s)) x =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P (arrow d)).level n (r, x)) s :=
  (comparison_native P d n r s x).trans
    (boundedFlatCoefficientBassPositiveTransitionHomotopy_apply P (arrow d) n r s x).symm

/-- Reverse comparison time once for the original J0 orientation, leaving path time unchanged. -/
def reverseComparison : (targetWord P d).Homotopy (sourceWord P d) :=
  (comparison P d).symm

/-- The J0-oriented scalar comparison has the transition image at exactly symm r and s. -/
theorem reverseComparison_transition (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (reverseComparison P d (r, s)) x =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P (arrow d)).level n
          (unitInterval.symm r, x)) s :=
  comparison_transition P d n (unitInterval.symm r) s x

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0Conjugation
