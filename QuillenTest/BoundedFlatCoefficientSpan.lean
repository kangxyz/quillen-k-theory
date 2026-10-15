/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSpanMap

/-! Original bounded-flat polynomial-span endpoints and Laurent tracks for arbitrary
coefficients. -/
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace QuillenTest.BoundedFlatCoefficientSpan

open Quillen

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

lemma original_left_endpoint :
    HomotopyPushout.inl _ _ ≫ boundedFlatPolynomialSpanMap f =
      boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inl _ _ :=
  inl_boundedFlatPolynomialSpanMap f

lemma original_right_endpoint :
    HomotopyPushout.inr _ _ ≫ boundedFlatPolynomialSpanMap f =
      boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inr _ _ :=
  inr_boundedFlatPolynomialSpanMap f

lemma original_span_structure (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatPolynomialSpanMap f).map (n + 1)
        (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) (n + 1)
          (s, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t)) =
      (HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (polynomialProjection S))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection S))).structureMap n
        ((boundedFlatPolynomialSpanMap f).map n
          (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n (s, x))) t :=
  congrArg (fun p ↦ p t) ((boundedFlatPolynomialSpanMap f).comm n
    (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n (s, x)))

lemma original_plus_start (n : ℕ)
    (x : (originalPrespectrum
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatPlusSquareHomotopy f).level n (0, x) =
      (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f))).map n
        ((boundedFlatPerfectPrespectrumMap (laurentPlus R)).map n x) :=
  (boundedFlatPlusSquareHomotopy f).at_zero n x

lemma original_minus_finish (n : ℕ)
    (x : (originalPrespectrum
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatMinusSquareHomotopy f).level n (1, x) =
      (boundedFlatPerfectPrespectrumMap (laurentMinus S)).map n
        ((boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f))).map n x) :=
  (boundedFlatMinusSquareHomotopy f).at_one n x

end QuillenTest.BoundedFlatCoefficientSpan
