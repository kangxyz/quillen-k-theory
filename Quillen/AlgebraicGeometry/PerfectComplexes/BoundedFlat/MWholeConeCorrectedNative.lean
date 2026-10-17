/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedSquare
public import Quillen.Topology.Prespectrum.ConeCompositionCorrectionEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyFactorEvaluation
public import Quillen.Topology.Prespectrum.CarrierCorrectedBoundaryEvaluation
public import Quillen.Topology.Prespectrum.CarrierSquareDescentEvaluation

/-! Exact native recovery of the frozen original M cone composition, with every clock retained. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier
open CommonReferenceNerve BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The native polynomial-span cylinder input at level `n` and overlap time `t`. -/
abbrev input (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :=
  HomotopyPushout.cylinder
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)

/-- Evaluate a scalar cone path at time `t` on the original prespectrum input `x`. -/
def evaluate (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (f : C(I, FourEdge.scalarCone P c (inputReference P p q))) :=
  FourEdge.coneEval P c (inputReference P p q) n (f t) x

/-- The first native piece of the coefficient Bass cone composition homotopy. -/
abbrev nativeFirst := ConeCompositionPieces.first
  (boundedFlatCoefficientBassSquareComparison P c)
  (boundedFlatCoefficientPolynomialSpanMap P p)
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
  (boundedFlatCoefficientBassComparisonHomotopy P p)
/-- The second native piece of the coefficient Bass cone composition homotopy. -/
abbrev nativeSecond := ConeCompositionPieces.second
  (boundedFlatCoefficientBassSquareComparison P c)
  (boundedFlatCoefficientPolynomialSpanMap P p)
  (boundedFlatCoefficientPolynomialSpanMap P q)
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
  (boundedFlatCoefficientBassComparisonHomotopy P q)
/-- The third native piece of the coefficient Bass cone composition homotopy. -/
abbrev nativeThird := ConeCompositionPieces.third
  (boundedFlatCoefficientBassSquareComparison P c)
  (boundedFlatCoefficientPolynomialSpanMap P p)
  (boundedFlatCoefficientPolynomialSpanMap P q)

theorem upperWord_native (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n t x (upperWord P p q s) =
    (((nativeFirst P p q).trans (nativeSecond P p q)).trans (nativeThird P p q)).level n
      (s, input P (a := a) n t x) := by
  rw [upperWord_apply]
  have h := (initial_native P p q n 1 s t x).trans
    ((initialNative P p q).at_one n s (input P (a := a) n t x))
  exact h.trans (congrArg (fun f ↦ f (s, input P (a := a) n t x))
    (ConeCompositionPieces.source_level
      (boundedFlatCoefficientBassSquareComparison P c)
      (boundedFlatCoefficientPolynomialSpanMap P p)
      (boundedFlatCoefficientPolynomialSpanMap P q)
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
      (boundedFlatCoefficientBassComparisonHomotopy P p)
      (boundedFlatCoefficientBassComparisonHomotopy P q) n))

private theorem firstTwo_native (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n t x (((firstPath P p q).trans (secondPath P p q)) s) =
      ((nativeFirst P p q).trans (nativeSecond P p q)).level n (s, input P (a := a) n t x) :=
  NativeFactorEvaluation.left_factor n (input P (a := a) n t x) (evaluate P p q n t x)
    ((firstPath P p q).trans (secondPath P p q)) (thirdPath P p q)
    ((nativeFirst P p q).trans (nativeSecond P p q)) (nativeThird P p q)
    (fun w ↦ by simpa only [upperWord] using upperWord_native P p q n t w x) s

/-- Full first-piece evaluation follows from the whole source word, including its midpoint. -/
theorem firstPath_native (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n t x (firstPath P p q s) =
      (nativeFirst P p q).level n (s, input P (a := a) n t x) :=
  NativeFactorEvaluation.left_factor n (input P (a := a) n t x) (evaluate P p q n t x)
    (firstPath P p q) (secondPath P p q) (nativeFirst P p q) (nativeSecond P p q)
    (fun w ↦ firstTwo_native P p q n t w x) s

/-- Full second-piece evaluation retains the native original associativity endpoint casts. -/
theorem secondPath_native (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n t x (secondPath P p q s) =
      (nativeSecond P p q).level n (s, input P (a := a) n t x) :=
  NativeFactorEvaluation.right_factor n (input P (a := a) n t x) (evaluate P p q n t x)
    (firstPath P p q) (secondPath P p q) (nativeFirst P p q) (nativeSecond P p q)
    (fun w ↦ firstTwo_native P p q n t w x) s

/-- Full final-cylinder evaluation, without deleting its original time coordinate. -/
theorem thirdPath_native (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n t x (thirdPath P p q s) =
      (nativeThird P p q).level n (s, input P (a := a) n t x) :=
  NativeFactorEvaluation.right_factor n (input P (a := a) n t x) (evaluate P p q n t x)
    ((firstPath P p q).trans (secondPath P p q)) (thirdPath P p q)
    ((nativeFirst P p q).trans (nativeSecond P p q)) (nativeThird P p q)
    (fun w ↦ by simpa only [upperWord] using upperWord_native P p q n t w x) s

/-- The native null comparison for coefficient Bass cone composition along `p` and `q`. -/
abbrev nativeCorrection := coneSquareCompositionNullComparison
  (boundedFlatCoefficientBassSquareComparison P a)
  (boundedFlatCoefficientBassSquareComparison P b)
  (boundedFlatCoefficientBassSquareComparison P c)
  (boundedFlatCoefficientPolynomialSpanMap P p)
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map p)))
  (boundedFlatCoefficientPolynomialSpanMap P q)
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
  (boundedFlatCoefficientBassComparisonHomotopy P p)
  (boundedFlatCoefficientBassComparisonHomotopy P q)

theorem correction_native (n : ℕ) (t r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n t x (correction P p q (r, s)) =
      (nativeCorrection P p q).level n (r, (s, input P (a := a) n t x)) := by
  have hc := Path.Evaluation.transAssoc (evaluate P p q n t x)
    (firstPath P p q) (secondPath P p q) (thirdPath P p q)
    ((nativeFirst P p q).path n (input P (a := a) n t x))
    ((nativeSecond P p q).path n (input P (a := a) n t x))
    ((nativeThird P p q).path n (input P (a := a) n t x))
    (fun w ↦ firstPath_native P p q n t w x)
    (fun w ↦ secondPath_native P p q n t w x)
    (fun w ↦ thirdPath_native P p q n t w x) r s
  exact hc.trans (ConeCompositionPieces.correction_apply
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P p)
    (boundedFlatCoefficientPolynomialSpanMap P q)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
    (boundedFlatCoefficientBassComparisonHomotopy P p)
    (boundedFlatCoefficientBassComparisonHomotopy P q) n r s (input P (a := a) n t x)).symm

/-- The corrected native boundary formed from the initial square and composition null comparison. -/
abbrev nativeBoundary :=
  CarrierPathSquare.nativeCorrectedBoundary (initialNative P p q) (nativeCorrection P p q)

theorem correctedBoundary_native (n : ℕ) (t r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n t x (correctedBoundary P p q (r, s)) =
      (nativeBoundary P p q).level n (r, (s, input P (a := a) n t x)) :=
  CarrierPathSquare.correctedBoundary_native
    (initialSquare P p q) (correction P p q) (initialNative P p q)
    (nativeCorrection P p q) n (input P (a := a) n t x) (evaluate P p q n t x)
    (fun r s ↦ initial_native P p q n r s t x)
    (fun r s ↦ correction_native P p q n t r s x) r s

/-- The native moving null square for coefficient Bass cone composition along `p` and `q`. -/
abbrev nativeNullSquare := coneSquareCompositionMovingNullSquare
  (boundedFlatCoefficientBassSquareComparison P a)
  (boundedFlatCoefficientBassSquareComparison P b)
  (boundedFlatCoefficientBassSquareComparison P c)
  (boundedFlatCoefficientPolynomialSpanMap P p)
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map p)))
  (boundedFlatCoefficientPolynomialSpanMap P q)
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
  (boundedFlatCoefficientBassComparisonHomotopy P p)
  (boundedFlatCoefficientBassComparisonHomotopy P q)
  (boundedFlatCoefficientBassComparisonHomotopy P (p ≫ q))
  (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q)
  (boundedFlatCoefficientLaurentCompositionHomotopy P p q)
  (BassMWhole.comparisonSquare P p q)

theorem nativeBoundary_toSquare :
    (nativeBoundary P p q).toSquare = nativeNullSquare P p q :=
  (coneSquareCompositionMovingNullSquare_eq_boundary
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P p)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map p)))
    (boundedFlatCoefficientPolynomialSpanMap P q)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
    (boundedFlatCoefficientBassComparisonHomotopy P p)
    (boundedFlatCoefficientBassComparisonHomotopy P q)
    (boundedFlatCoefficientBassComparisonHomotopy P (p ≫ q))
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q)
    (boundedFlatCoefficientLaurentCompositionHomotopy P p q)
    (BassMWhole.comparisonSquare P p q)).symm

theorem corrected_native (n : ℕ) (r s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P c (inputReference P p q) n (corrected P p q (r, (s, t))) x =
      (nativeNullSquare P p q).level n (r, (s, input P (a := a) n t x)) := by
  have h := CarrierPathSquare.boundarySquare_native (correctedBoundary P p q)
    (nativeBoundary P p q) n (input P (a := a) n t x) (evaluate P p q n t x)
    (fun r s ↦ correctedBoundary_native P p q n t r s x) r s
  exact h.trans (congrArg (fun S ↦ S.level n (r, (s, input P (a := a) n t x)))
    (nativeBoundary_toSquare P p q))

/-- This is the selected old coneComposition cylinder, with all four coordinates independent. -/
theorem coneComposition_cylinder (n : ℕ) (r s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P c (inputReference P p q) n (corrected P p q (r, (s, t))) x =
      (BassMWhole.coneComposition P p q).level n
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatCoefficientBassSquareComparison P a).map n)
          (s, input P (a := a) n t x)) := by
  rw [corrected_native]
  rfl

end Quillen.PerfectComplexes.BassMWholeConeCarrier
