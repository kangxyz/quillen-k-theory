/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrackProjection
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSpanMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSquare
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting

/-! Genuine double-square pasting for both original Laurent coefficient diagrams. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original outer Laurent projection square is common to both chart diagrams. -/
def boundedFlatLaurentCoefficientSquareHomotopy :=
  boundedFlatPerfectPrespectrumSquareHomotopy (Spec.map (laurentMap f))
    (laurentProjection R) (laurentProjection S) (Spec.map f) (laurentMap_projection f)

/-- Paste the original plus Laurent square and the original polynomial square. -/
def boundedFlatPlusCoefficientLeftTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPlusSquareHomotopy f)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatPolynomialSquareHomotopy f).postcomp
      (boundedFlatPerfectPrespectrumMap (laurentPlus S)))

/-- The plus route through the common original Laurent projection square. -/
def boundedFlatPlusCoefficientRightTrack :=
  ((boundedFlatLaurentPlusHomotopy R).postcomp
    (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))).symm.trans
    ((boundedFlatLaurentCoefficientSquareHomotopy f).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
        (boundedFlatLaurentPlusHomotopy S)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original plus coefficient tracks and common outer square. -/
def boundedFlatPlusCoefficientPasting :
    (boundedFlatPlusCoefficientLeftTrack f).RelHomotopy
      (boundedFlatPlusCoefficientRightTrack f) :=
  DoubleSquareTrack.projectionComparison (polynomialProjection R) (laurentPlus R)
    (polynomialProjection S) (laurentPlus S) (Spec.map f)
    (Spec.map (polynomialMap f)) (Spec.map (laurentMap f))
    (polynomialMap_projection f) (laurentMap_plus f)
    (laurentProjection R) (laurentProjection S)
    (laurentPlus_projection R) (laurentPlus_projection S)

/-- Paste the original minus Laurent square and the original polynomial square. -/
def boundedFlatMinusCoefficientLeftTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatMinusSquareHomotopy f)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatPolynomialSquareHomotopy f).postcomp
      (boundedFlatPerfectPrespectrumMap (laurentMinus S)))

/-- The minus route through the common original Laurent projection square. -/
def boundedFlatMinusCoefficientRightTrack :=
  ((boundedFlatLaurentMinusHomotopy R).postcomp
    (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))).symm.trans
    ((boundedFlatLaurentCoefficientSquareHomotopy f).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
        (boundedFlatLaurentMinusHomotopy S)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original minus coefficient tracks and common outer square. -/
def boundedFlatMinusCoefficientPasting :
    (boundedFlatMinusCoefficientLeftTrack f).RelHomotopy
      (boundedFlatMinusCoefficientRightTrack f) :=
  DoubleSquareTrack.projectionComparison (polynomialProjection R) (laurentMinus R)
    (polynomialProjection S) (laurentMinus S) (Spec.map f)
    (Spec.map (polynomialMap f)) (Spec.map (laurentMap f))
    (polynomialMap_projection f) (laurentMap_minus f)
    (laurentProjection R) (laurentProjection S)
    (laurentMinus_projection R) (laurentMinus_projection S)

/-- The two genuine Laurent coefficient pastings cancel their common outer square and give
an actual relative boundary comparison, retaining the prescribed concatenation associations. -/
def boundedFlatBassCoefficientBoundary :=
  Homotopy.RelHomotopy.pasteTwoSquares
    (boundedFlatPlusCoefficientPasting f) (boundedFlatMinusCoefficientPasting f)

end Quillen.PerfectComplexes
