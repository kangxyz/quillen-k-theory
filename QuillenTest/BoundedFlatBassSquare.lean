/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSquare

/-! The raw Bass comparison retains both actual Laurent endpoint maps and its entire cylinder. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.BoundedFlatBassSquare

open Quillen

/-- The positive endpoint remains the literal original Laurent pullback throughout comparison. -/
theorem original_plus_endpoint (R : CommRingCat.{u}) (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatBassSquareComparisonNormalization R).level n
      (r, (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).map n x) =
      (boundedFlatPerfectPrespectrumMap (laurentPlus R)).map n x := rfl

/-- The negative endpoint retains its own original inverse-coordinate Laurent pullback. -/
theorem original_minus_endpoint (R : CommRingCat.{u}) (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatBassSquareComparisonNormalization R).level n
      (r, (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).map n x) =
      (boundedFlatPerfectPrespectrumMap (laurentMinus R)).map n x := rfl

/-- The whole original cylinder retains both independent times of its actual Bass-track filler. -/
theorem original_cylinder_track (R : CommRingCat.{u}) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassSquareComparisonNormalization R).level n
      (r, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n (s, x)) =
      (boundedFlatBassSquareNormalization R).level n (r, (s, x)) := rfl

end QuillenTest.BoundedFlatBassSquare
