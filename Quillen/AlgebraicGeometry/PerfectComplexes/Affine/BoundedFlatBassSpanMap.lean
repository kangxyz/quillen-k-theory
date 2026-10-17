/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Flat
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare

/-!
# Actual bounded-flat polynomial-span maps under arbitrary coefficient change

Every coefficient homomorphism induces original bounded-flat pullback maps. The actual geometric
squares give the full tracks needed to map the two-chart homotopy pushout, retaining both literal
endpoint maps and the whole cylinder. Positive and inverse-coordinate Laurent tracks are retained
separately. No flat coefficient hypothesis is required. Perfect-model comparison and Bass transition
naturality remain separate.
-/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent


noncomputable section

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.IteratedS

universe u

namespace Quillen.PerfectComplexes

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- This is the original polynomial square, with its actual arbitrary-map bounded-flat pullbacks. -/
def boundedFlatPolynomialSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
      boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)))
    (boundedFlatPerfectPrespectrumMap (Spec.map f) ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection S)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _ (polynomialMap_projection f)

/-- Arbitrary coefficient change supplies an actual map of the two polynomial-chart pushouts. -/
def boundedFlatPolynomialSpanMap :
    HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) ⟶
      HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (polynomialProjection S))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection S)) :=
  HomotopyPushout.mapOfHomotopies _ _ _ _ (boundedFlatPerfectPrespectrumMap (Spec.map f))
    (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)))
    (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)))
    (boundedFlatPolynomialSquareHomotopy f) (boundedFlatPolynomialSquareHomotopy f)

/-- The original left polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inl_boundedFlatPolynomialSpanMap :
    HomotopyPushout.inl _ _ ≫ boundedFlatPolynomialSpanMap f =
      boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inl _ _ :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The original right polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inr_boundedFlatPolynomialSpanMap :
    HomotopyPushout.inr _ _ ≫ boundedFlatPolynomialSpanMap f =
      boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inr _ _ :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- Every cylinder point retains the original pasted geometric comparison tracks. -/
lemma boundedFlatPolynomialSpanMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatPolynomialSpanMap f).map n
        (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n (s, x)) =
      (HomotopyPushout.mapSquareHomotopy _ _ _ _ (boundedFlatPerfectPrespectrumMap (Spec.map f))
        (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)))
        (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)))
        (boundedFlatPolynomialSquareHomotopy f) (boundedFlatPolynomialSquareHomotopy f)).level n
          (s, x) := rfl

/-- The positive Laurent chart retains its actual geometric square. -/
def boundedFlatPlusSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (laurentPlus R) ≫
      boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))
    (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus S)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _ (laurentMap_plus f)

/-- The inverse-coordinate Laurent chart retains its actual geometric square. -/
def boundedFlatMinusSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (laurentMinus R) ≫
      boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))
    (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫
      boundedFlatPerfectPrespectrumMap (laurentMinus S)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _ (laurentMap_minus f)

end Quillen.PerfectComplexes
