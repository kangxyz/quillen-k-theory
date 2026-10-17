/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.CarrierCorrectedBoundaryEvaluation
public import Quillen.Topology.Prespectrum.CarrierSquareDescentEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1ShiftedCorrectedBoundary

/-! Whole shifted corrected-boundary evaluation and the original null-square identification. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1ShiftedCorrectedNative
open CoefficientBassPositiveC1ShiftedReassociationPieces
open CoefficientBassPositiveC1ShiftedCorrectedBoundary
open CoefficientBassPositiveC1ShiftedInitialMovingNull
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The exact original native boundary tree, prior to its final quotient descent. -/
abbrev nativeBoundary :=
  CarrierPathSquare.nativeCorrectedBoundary (initialNative P p q) (nativeCorrection P p q)

/-- The whole shifted corrected boundary has the original native image at every coordinate. -/
theorem correctedBoundary_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x (correctedBoundary P p q (r, s)) =
      (nativeBoundary P p q).level n (r, (s, input P n x)) := by
  exact CarrierPathSquare.correctedBoundary_native
    (initialSquare P p q) (correction P p q) (initialNative P p q)
    (nativeCorrection P p q) n (input P n x) (evaluate P p q n x)
    (fun r s ↦ parameter_native P p q n r s x)
    (fun r s ↦ correction_native P p q n r s x) r s

/-- The final native wrapper is identified at abstract maps before this specialization. -/
theorem nativeBoundary_toSquare :
    (nativeBoundary P p q).toSquare =
      CoefficientBassPositiveCompositionTrack.nullSquare P p q := by
  exact (coneSquareCompositionMovingNullSquare_eq_boundary
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map p)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
    (boundedFlatCoefficientPlusSquareHomotopy P p)
    (boundedFlatCoefficientPlusSquareHomotopy P q)
    (boundedFlatCoefficientPlusSquareHomotopy P (p ≫ q))
    (CoefficientBassPositiveCompositionTrack.polynomialComposition P p q)
    (boundedFlatCoefficientLaurentCompositionHomotopy P p q)
    (CoefficientBassPositiveCompositionTrack.comparisonSquare P p q)).symm

/-- Descent recovers the original corrected null square without evaluator continuity. -/
theorem correctedSquare_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x ((correctedSquare P p q).parameter (r, s)) =
      (CoefficientBassPositiveCompositionTrack.nullSquare P p q).level n
        (r, (s, input P n x)) := by
  have h := CarrierPathSquare.boundarySquare_native (correctedBoundary P p q)
    (nativeBoundary P p q) n (input P n x) (evaluate P p q n x)
    (fun r s ↦ correctedBoundary_native P p q n r s x) r s
  exact h.trans (congrArg (fun S ↦ S.level n (r, (s, input P n x)))
    (nativeBoundary_toSquare P p q))

end Quillen.PerfectComplexes.CoefficientBassPositiveC1ShiftedCorrectedNative
