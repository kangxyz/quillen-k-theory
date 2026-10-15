/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurentFlat
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.FlatSquare
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare

/-!
# Actual polynomial-span spectrum maps under flat coefficient change

The original geometric flat squares supply whole spectrum homotopies. These produce a map of the
actual two-polynomial-chart homotopy pushouts, with literal endpoint maps and the entire cylinder
track retained. The two Laurent chart square homotopies are also supplied separately. Compatibility
with the Bass square comparison or its transition requires further higher coherence.
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

variable {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)]

/-- This is the original polynomial square, with its actual geometric flat maps. -/
def polynomialSquareHomotopy : Homotopy
    (perfectFlatPrespectrumMap (polynomialProjection R) ≫
      perfectFlatPrespectrumMap (Spec.map (polynomialMap f)))
    (perfectFlatPrespectrumMap (Spec.map f) ≫
      perfectFlatPrespectrumMap (polynomialProjection S)) :=
  perfectFlatPrespectrumSquareHomotopy _ _ _ _ (polynomialMap_projection f)

/-- Flat coefficient change supplies an actual map of the two polynomial-chart pushouts. -/
def polynomialSpanMap :
    HomotopyPushout.prespectrum (perfectFlatPrespectrumMap (polynomialProjection R))
        (perfectFlatPrespectrumMap (polynomialProjection R)) ⟶
      HomotopyPushout.prespectrum (perfectFlatPrespectrumMap (polynomialProjection S))
        (perfectFlatPrespectrumMap (polynomialProjection S)) :=
  HomotopyPushout.mapOfHomotopies _ _ _ _ (perfectFlatPrespectrumMap (Spec.map f))
    (perfectFlatPrespectrumMap (Spec.map (polynomialMap f)))
    (perfectFlatPrespectrumMap (Spec.map (polynomialMap f)))
    (polynomialSquareHomotopy f) (polynomialSquareHomotopy f)

/-- The original left polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inl_polynomialSpanMap :
    HomotopyPushout.inl _ _ ≫ polynomialSpanMap f =
      perfectFlatPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inl _ _ :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The original right polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inr_polynomialSpanMap :
    HomotopyPushout.inr _ _ ≫ polynomialSpanMap f =
      perfectFlatPrespectrumMap (Spec.map (polynomialMap f)) ≫ HomotopyPushout.inr _ _ :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- Every cylinder point retains the original pasted geometric comparison tracks. -/
lemma polynomialSpanMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen (Spec R))).space n) :
    (polynomialSpanMap f).map n
        (HomotopyPushout.cylinder (perfectFlatPrespectrumMap (polynomialProjection R))
          (perfectFlatPrespectrumMap (polynomialProjection R)) n (s, x)) =
      (HomotopyPushout.mapSquareHomotopy _ _ _ _ (perfectFlatPrespectrumMap (Spec.map f))
        (perfectFlatPrespectrumMap (Spec.map (polynomialMap f)))
        (perfectFlatPrespectrumMap (Spec.map (polynomialMap f)))
        (polynomialSquareHomotopy f) (polynomialSquareHomotopy f)).level n (s, x) := rfl

/-- The positive Laurent chart retains its actual flat geometric square. -/
def plusSquareHomotopy : Homotopy
    (perfectFlatPrespectrumMap (laurentPlus R) ≫
      perfectFlatPrespectrumMap (Spec.map (laurentMap f)))
    (perfectFlatPrespectrumMap (Spec.map (polynomialMap f)) ≫
      perfectFlatPrespectrumMap (laurentPlus S)) :=
  perfectFlatPrespectrumSquareHomotopy _ _ _ _ (laurentMap_plus f)

/-- The inverse-coordinate Laurent chart retains its actual flat geometric square. -/
def minusSquareHomotopy : Homotopy
    (perfectFlatPrespectrumMap (laurentMinus R) ≫
      perfectFlatPrespectrumMap (Spec.map (laurentMap f)))
    (perfectFlatPrespectrumMap (Spec.map (polynomialMap f)) ≫
      perfectFlatPrespectrumMap (laurentMinus S)) :=
  perfectFlatPrespectrumSquareHomotopy _ _ _ _ (laurentMap_minus f)

end Quillen.PerfectComplexes
