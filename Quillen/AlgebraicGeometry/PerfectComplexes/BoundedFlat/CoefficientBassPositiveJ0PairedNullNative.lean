/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PairedNull
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0ConePasting

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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0PairedNullNative
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0PairedNull
open CoefficientBassPositiveJ0ConePasting
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The retyped minus cone comparison retains the complete original native conePasting. -/
theorem coneComparisonMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (coneComparisonMinus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.conePasting P (arrow d)).level n (r, (s, x)) := by
  rw [coneComparisonMinus_apply]
  exact coneBoundaryMinus_conePasting P d n r s x

/-- The whole retyped old cone uses the same cylinder and its own original tip. -/
theorem oldConeMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (oldConeMinus P d s) x =
      (CoefficientBassPositiveNullTrack.oldCone P (arrow d)).level n (s, x) :=
  (squareMinus_native P d n 0 s x).trans ((nativeSquare P d n x).at_zero s)

/-- The whole retyped new cone keeps the original terminal transport and its separate tip. -/
theorem newConeMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (newConeMinus P d s) x =
      (CoefficientBassPositiveNullTrack.newCone P (arrow d)).level n (s, x) :=
  (squareMinus_native P d n 1 s x).trans ((nativeSquare P d n x).at_one s)

/-- The whole polynomial rail follows from its exact cone-square seam, at every input. -/
theorem polynomialMovementMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (polynomialMovementMinus P d s) x =
      (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d)).level n (s, x) := by
  rw [polynomialMinus_seam]
  exact (squareMinus_native P d n s 0 x).trans ((nativeSquare P d n x).left s)

/-- The retyped plus cone comparison retains the complete original native conePasting. -/
theorem coneComparisonPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (coneComparisonPlus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.conePasting P (arrow d)).level n (r, (s, x)) := by
  rw [coneComparisonPlus_apply]
  exact coneBoundaryPlus_conePasting P d n r s x

/-- The whole retyped old cone uses the same cylinder and its own original tip. -/
theorem oldConePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (oldConePlus P d s) x =
      (CoefficientBassPositiveNullTrack.oldCone P (arrow d)).level n (s, x) :=
  (squarePlus_native P d n 0 s x).trans ((nativeSquare P d n x).at_zero s)

/-- The whole retyped new cone keeps the original terminal transport and its separate tip. -/
theorem newConePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (newConePlus P d s) x =
      (CoefficientBassPositiveNullTrack.newCone P (arrow d)).level n (s, x) :=
  (squarePlus_native P d n 1 s x).trans ((nativeSquare P d n x).at_one s)

/-- The whole polynomial rail follows from its exact cone-square seam, at every input. -/
theorem polynomialMovementPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (polynomialMovementPlus P d s) x =
      (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d)).level n (s, x) := by
  rw [polynomialPlus_seam]
  exact (squarePlus_native P d n s 0 x).trans ((nativeSquare P d n x).left s)

/-- The unchanged original ofLevels transport leaves both interior coordinates untouched. -/
theorem originalNullComparison_apply (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    (CoefficientBassPositiveNullTrack.originalNullComparison P (arrow d)).level n (r, (s, x)) =
      (CoefficientBassPositiveNullTrack.pastedNullComparison P (arrow d)).level n
        (r, (s, x)) := by
  unfold CoefficientBassPositiveNullTrack.originalNullComparison
  rw [LoopPrespectrum.Homotopy.RelHomotopy.ofLevels_apply]

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0PairedNullNative
