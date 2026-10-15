/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSpanMap

/-! Genuine Laurent coefficient triples retain original tracks and independent structure time. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BassTripleTrack

open Quillen
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The positive Laurent initial face is literally the original left binary-composition route. -/
theorem plus_initial (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatTripleTrackComparison (laurentPlus S) (polynomialProjection S) (Spec.map f)).level n
      (0, (s, x)) =
    ((boundedFlatPerfectPrespectrumCompHomotopy (laurentPlus S)
      (polynomialProjection S ≫ Spec.map f)).trans
      ((boundedFlatPerfectPrespectrumCompHomotopy (polynomialProjection S) (Spec.map f)).postcomp
        (boundedFlatPerfectPrespectrumMap (laurentPlus S)))).level n (s, x) :=
  ((boundedFlatTripleTrackComparison (laurentPlus S) (polynomialProjection S)
    (Spec.map f)).level n).apply_zero _

/-- The negative Laurent final face retains the original right route with explicit transport. -/
theorem minus_final (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatTripleTrackComparison (laurentMinus S) (polynomialProjection S)
      (Spec.map f)).level n (1, (s, x)) =
    (((boundedFlatPerfectPrespectrumCompHomotopy (laurentMinus S ≫ polynomialProjection S)
        (Spec.map f)).trans
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
        (boundedFlatPerfectPrespectrumCompHomotopy (laurentMinus S) (polynomialProjection S)))).cast
      (congrArg boundedFlatPerfectPrespectrumMap (Category.assoc _ _ _))
      (Category.assoc _ _ _).symm).level n (s, x) :=
  ((boundedFlatTripleTrackComparison (laurentMinus S) (polynomialProjection S)
    (Spec.map f)).level n).apply_one _

/-- Comparison, original path and suspension coordinates are genuinely independent. -/
theorem plus_structure (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatTripleTrackComparison (laurentPlus S) (polynomialProjection S) (Spec.map f)).level
      (n + 1) (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap
        n x t)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (Spec (.of (LaurentPolynomial S))))).structureMap n
        ((boundedFlatTripleTrackComparison (laurentPlus S) (polynomialProjection S)
          (Spec.map f)).level n (r, (s, x))) t :=
  (boundedFlatTripleTrackComparison (laurentPlus S) (polynomialProjection S)
    (Spec.map f)).comm n r s x t

end QuillenTest.BassTripleTrack
