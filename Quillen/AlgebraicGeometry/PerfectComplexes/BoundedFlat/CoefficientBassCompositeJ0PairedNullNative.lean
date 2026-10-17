/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0PairedNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0ConePasting

/-!
# Concrete native cone constituents and the original null-comparison transport

The ordinary and shifted cone comparisons keep their separate carrier tips. All equalities
retain every level, source input and both times. The full nested native null comparison still
requires the remaining positive rail identities and native path-operation bridges.
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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0PairedNullNative
open CommonReferenceNerve CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0PairedNull
open CoefficientBassCompositeJ0ConePasting
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The retyped minus cone comparison retains the complete original native conePasting. -/
theorem coneComparisonMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (coneComparisonMinus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.conePasting P (arrow p q)).level n (r, (s, x)) := by
  rw [coneComparisonMinus_apply]
  exact coneBoundaryMinus_conePasting P p q n r s x

/-- The whole retyped old cone uses the same cylinder and its own original tip. -/
theorem oldConeMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (oldConeMinus P p q s) x =
      (CoefficientBassPositiveNullTrack.oldCone P (arrow p q)).level n (s, x) :=
  (squareMinus_native P p q n 0 s x).trans ((nativeSquare P p q n x).at_zero s)

/-- The whole retyped new cone keeps the original terminal transport and its separate tip. -/
theorem newConeMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (newConeMinus P p q s) x =
      (CoefficientBassPositiveNullTrack.newCone P (arrow p q)).level n (s, x) :=
  (squareMinus_native P p q n 1 s x).trans ((nativeSquare P p q n x).at_one s)

/-- The whole polynomial rail follows from its exact cone-square seam, at every input. -/
theorem polynomialMovementMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (polynomialMovementMinus P p q s) x =
      (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q)).level n (s, x) := by
  rw [polynomialMinus_seam]
  exact (squareMinus_native P p q n s 0 x).trans ((nativeSquare P p q n x).left s)

/-- The retyped plus cone comparison retains the complete original native conePasting. -/
theorem coneComparisonPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (coneComparisonPlus P p q (r, s)) x =
      (CoefficientBassPositiveNullTrack.conePasting P (arrow p q)).level n (r, (s, x)) := by
  rw [coneComparisonPlus_apply]
  exact coneBoundaryPlus_conePasting P p q n r s x

/-- The whole retyped old cone uses the same cylinder and its own original tip. -/
theorem oldConePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (oldConePlus P p q s) x =
      (CoefficientBassPositiveNullTrack.oldCone P (arrow p q)).level n (s, x) :=
  (squarePlus_native P p q n 0 s x).trans ((nativeSquare P p q n x).at_zero s)

/-- The whole retyped new cone keeps the original terminal transport and its separate tip. -/
theorem newConePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (newConePlus P p q s) x =
      (CoefficientBassPositiveNullTrack.newCone P (arrow p q)).level n (s, x) :=
  (squarePlus_native P p q n 1 s x).trans ((nativeSquare P p q n x).at_one s)

/-- The whole polynomial rail follows from its exact cone-square seam, at every input. -/
theorem polynomialMovementPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (polynomialMovementPlus P p q s) x =
      (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q)).level n (s, x) := by
  rw [polynomialPlus_seam]
  exact (squarePlus_native P p q n s 0 x).trans ((nativeSquare P p q n x).left s)

/-- The unchanged original ofLevels transport leaves both interior coordinates untouched. -/
theorem originalNullComparison_apply (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow p q)).level n (r, (s, x)) =
      (CoefficientBassPositiveNullTrack.pastedNullComparison P (arrow p q)).level n
        (r, (s, x)) := by
  unfold CoefficientBassPositiveNullTrack.originalNullComparison
  rw [LoopPrespectrum.Homotopy.RelHomotopy.ofLevels_apply]

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0PairedNullNative
