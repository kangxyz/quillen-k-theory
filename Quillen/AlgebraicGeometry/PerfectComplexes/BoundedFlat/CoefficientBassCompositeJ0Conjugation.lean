/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopyTwoSheetConjugationEvaluation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0TypedUnitRails

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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0Conjugation
open CommonReferenceNerve CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0PairedNull
open CoefficientBassCompositeJ0TypedUnitRails CoefficientBassCompositeJ0FullNullNative
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The endpoint-retyped old unit retains the complete original V parameter. -/
theorem oldUnit_apply (s : I) : oldUnit P p q s =
    CoefficientBassCompositeJ0RectangleRails.unitMap P p q
      (CoefficientLaurentUnitTenNodes.V s) := rfl

/-- The endpoint-retyped new unit retains the complete original W parameter. -/
theorem newUnit_apply (s : I) : newUnit P p q s =
    CoefficientBassCompositeJ0RectangleRails.unitMap P p q
      (CoefficientLaurentUnitTenNodes.W s) := rfl

/-- The complete old conjugate word joins the two distinct carrier tips. -/
abbrev sourceWord := (oldNullMinus P p q).symm.trans ((oldUnit P p q).trans (oldNullPlus P p q))

/-- The complete new conjugate word retains the same two distinct carrier tips. -/
abbrev targetWord := (newNullMinus P p q).symm.trans ((newUnit P p q).trans (newNullPlus P p q))

/-- The literal original conjugation is assembled from actual whole unit and null comparisons. -/
def comparison : (sourceWord P p q).Homotopy (targetWord P p q) :=
  Path.Homotopy.TwoSheetConjugation.comparison (oldUnit P p q) (newUnit P p q)
    (laurentMovementMinus P p q) (laurentMovementPlus P p q)
    (oldNullMinus P p q) (oldNullPlus P p q) (newNullMinus P p q) (newNullPlus P p q)
    (unitComparison P p q) (pastedNullMinus P p q) (pastedNullPlus P p q)

/-- Every level, input and independent pair of times has the original conjugateComparison image. -/
theorem comparison_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (comparison P p q (r, s)) x =
      (CoefficientBassPositiveTransitionTrack.conjugateComparison P (arrow p q)).level n
        (r, (s, x)) := by
  let E := originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))
  let F := LoopPrespectrum.mappingCone
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  let ev : Carrier P p q → F.space n := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  exact NativeTwoSheetConjugation.comparison (E := E) (T := F) n x ev
    (oldUnit P p q) (newUnit P p q) (laurentMovementMinus P p q) (laurentMovementPlus P p q)
    (oldNullMinus P p q) (oldNullPlus P p q) (newNullMinus P p q) (newNullPlus P p q)
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q))
    (CoefficientBassPositiveTransitionTrack.oldUnit P (arrow p q))
    (CoefficientBassPositiveTransitionTrack.newUnit P (arrow p q))
    (CoefficientBassPositiveNullTrack.originalOldNull P (arrow p q))
    (CoefficientBassPositiveNullTrack.originalNewNull P (arrow p q))
    (unitComparison P p q) (pastedNullMinus P p q) (pastedNullPlus P p q)
    (CoefficientBassPositiveTransitionTrack.unitPasting P (arrow p q))
    (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow p q))
    (fun t ↦ oldUnit_native P p q n t x) (fun t ↦ newUnit_native P p q n t x)
    (fun t ↦ movementMinus_native P p q n t x) (fun t ↦ movementPlus_native P p q n t x)
    (fun t ↦ newNullMinus_native P p q n t x) (fun t ↦ newNullPlus_native P p q n t x)
    (fun a b ↦ unitComparison_native P p q n a b x)
    (fun a b ↦ originalNullMinus_native P p q n a b x)
    (fun a b ↦ originalNullPlus_native P p q n a b x) r s

/-- Original zero-loop-map and endpoint casts retain this complete native comparison. -/
theorem comparison_transition (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (comparison P p q (r, s)) x =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P (arrow p q)).level n (r, x)) s :=
  (comparison_native P p q n r s x).trans
    (boundedFlatCoefficientBassPositiveTransitionHomotopy_apply P (arrow p q) n r s x).symm

/-- Reverse comparison time once for the original J0 orientation, leaving path time unchanged. -/
def reverseComparison : (targetWord P p q).Homotopy (sourceWord P p q) :=
  (comparison P p q).symm

/-- The J0-oriented scalar comparison has the transition image at exactly symm r and s. -/
theorem reverseComparison_transition (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (reverseComparison P p q (r, s)) x =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P (arrow p q)).level n
          (unitInterval.symm r, x)) s :=
  comparison_transition P p q n (unitInterval.symm r) s x

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0Conjugation
