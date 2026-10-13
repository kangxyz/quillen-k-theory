/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CompositionTrack
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurent
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Quillen.Topology.Prespectrum.PushoutHomotopy

/-!
# The actual bounded-flat Bass square and its total-normalization comparison

Both Laurent legs retain their separate original geometric binary tracks. The full relative
comparison with their total normalized transformations descends to the actual double-cylinder
comparison maps. Coefficient-map naturality and the moving-boundary descent are further claims.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The positive leg retains its actual geometric-plus-binary-normalization track. -/
def boundedFlatLaurentPlusHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus R)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (laurentPlus R) (polynomialProjection R)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (laurentPlus_projection R)) rfl

/-- The inverse-coordinate leg retains its separate original binary track. -/
def boundedFlatLaurentMinusHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (laurentMinus R)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (laurentMinus R) (polynomialProjection R)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (laurentMinus_projection R)) rfl

/-- The total normalized positive geometric comparison, on the same literal endpoint maps. -/
def boundedFlatNormalizedLaurentPlusHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus R)) :=
  (boundedFlatNormalizedCompTrack (laurentPlus R) (polynomialProjection R)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (laurentPlus_projection R)) rfl

/-- The total normalized inverse-coordinate comparison, on the same literal endpoint maps. -/
def boundedFlatNormalizedLaurentMinusHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (laurentMinus R)) :=
  (boundedFlatNormalizedCompTrack (laurentMinus R) (polynomialProjection R)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (laurentMinus_projection R)) rfl

/-- The actual original two-leg Bass square in the raw bounded-flat model. -/
def boundedFlatBassSquareHomotopy (R : CommRingCat.{u}) :=
  (boundedFlatLaurentPlusHomotopy R).symm.trans (boundedFlatLaurentMinusHomotopy R)

/-- The same geometric square formed using the total normalized transformations. -/
def boundedFlatNormalizedBassSquareHomotopy (R : CommRingCat.{u}) :=
  (boundedFlatNormalizedLaurentPlusHomotopy R).symm.trans
    (boundedFlatNormalizedLaurentMinusHomotopy R)

/-- A whole relative comparison retains both original Laurent-leg tracks and their signs. -/
def boundedFlatBassSquareNormalization (R : CommRingCat.{u}) :
    (boundedFlatNormalizedBassSquareHomotopy R).RelHomotopy
      (boundedFlatBassSquareHomotopy R) :=
  ((boundedFlatNormalizedCompTrackComparison (laurentPlus R) (polynomialProjection R)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (laurentPlus_projection R)) rfl).symmPath.hcomp
    ((boundedFlatNormalizedCompTrackComparison (laurentMinus R) (polynomialProjection R)).cast
      (congrArg boundedFlatPerfectPrespectrumMap (laurentMinus_projection R)) rfl)

/-- The actual original double-cylinder comparison for the raw bounded-flat Bass square. -/
def boundedFlatBassSquareComparison (R : CommRingCat.{u}) :=
  HomotopyPushout.desc (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (laurentPlus R))
    (boundedFlatPerfectPrespectrumMap (laurentMinus R)) (boundedFlatBassSquareHomotopy R)

/-- The same endpoint maps descend using the total normalized square track. -/
def boundedFlatNormalizedBassSquareComparison (R : CommRingCat.{u}) :=
  HomotopyPushout.desc (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (laurentPlus R))
    (boundedFlatPerfectPrespectrumMap (laurentMinus R)) (boundedFlatNormalizedBassSquareHomotopy R)

/-- The genuine full relative Bass-track comparison descends to its original comparison maps. -/
def boundedFlatBassSquareComparisonNormalization (R : CommRingCat.{u}) :
    Homotopy (boundedFlatNormalizedBassSquareComparison R) (boundedFlatBassSquareComparison R) :=
  HomotopyPushout.descHomotopy _ _ _ _ (boundedFlatBassSquareNormalization R)

end Quillen.PerfectComplexes
