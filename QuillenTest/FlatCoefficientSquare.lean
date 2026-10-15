/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassSpanMap

/-! Consumers of the public original polynomial-span map and its supplied Laurent square tracks. -/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent


noncomputable section

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace QuillenTest.FlatCoefficientSquare

open Quillen

variable {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)]

lemma original_left_endpoint :
    HomotopyPushout.inl _ _ ≫ polynomialSpanMap f =
      perfectFlatPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inl _ _ :=
  inl_polynomialSpanMap f

lemma original_right_endpoint :
    HomotopyPushout.inr _ _ ≫ polynomialSpanMap f =
      perfectFlatPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inr _ _ :=
  inr_polynomialSpanMap f

lemma original_span_structure (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen (Spec R))).space n) :
    (polynomialSpanMap f).map (n + 1)
        (HomotopyPushout.cylinder (perfectFlatPrespectrumMap (polynomialProjection R))
          (perfectFlatPrespectrumMap (polynomialProjection R)) (n + 1)
          (s, (originalPrespectrum (perfectWaldhausen (Spec R))).structureMap n x t)) =
      (HomotopyPushout.prespectrum (perfectFlatPrespectrumMap (polynomialProjection S))
        (perfectFlatPrespectrumMap (polynomialProjection S))).structureMap n
        ((polynomialSpanMap f).map n
          (HomotopyPushout.cylinder (perfectFlatPrespectrumMap (polynomialProjection R))
            (perfectFlatPrespectrumMap (polynomialProjection R)) n (s, x))) t :=
  congrArg (fun p ↦ p t) ((polynomialSpanMap f).comm n
    (HomotopyPushout.cylinder (perfectFlatPrespectrumMap (polynomialProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R)) n (s, x)))

lemma original_plus_start (n : ℕ)
    (x : (originalPrespectrum
      (perfectWaldhausen (Spec (.of (Polynomial R))))).space n) :
    (plusSquareHomotopy f).level n (0, x) =
      (perfectFlatPrespectrumMap (Spec.map (laurentMap f))).map n
        ((perfectFlatPrespectrumMap (laurentPlus R)).map n x) :=
  (plusSquareHomotopy f).at_zero n x

lemma original_minus_finish (n : ℕ)
    (x : (originalPrespectrum
      (perfectWaldhausen (Spec (.of (Polynomial R))))).space n) :
    (minusSquareHomotopy f).level n (1, x) =
      (perfectFlatPrespectrumMap (laurentMinus S)).map n
        ((perfectFlatPrespectrumMap (Spec.map (polynomialMap f))).map n x) :=
  (minusSquareHomotopy f).at_one n x

end QuillenTest.FlatCoefficientSquare
