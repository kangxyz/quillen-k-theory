/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrackProjection
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare

/-!
# Original global raw Bass input charts

Every scheme arrow acts on the original polynomial span and the two original Laurent charts.
The whole chart pastings are specialized from the actual geometric double-square comparison.
No section evaluation or conjugation through an equivalence is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- This is the original polynomial square, with its actual arbitrary-map bounded-flat pullbacks. -/
def polynomialSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (projection.app Y) ≫
      boundedFlatPerfectPrespectrumMap (polynomial.map g))
    (boundedFlatPerfectPrespectrumMap g ≫
      boundedFlatPerfectPrespectrumMap (projection.app X)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _
    (projection.naturality g)

/-- Arbitrary scheme change supplies an actual map of the two polynomial-chart pushouts. -/
def spanMap :
    HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y)) ⟶
      HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X)) :=
  HomotopyPushout.mapOfHomotopies _ _ _ _ (boundedFlatPerfectPrespectrumMap g)
    (boundedFlatPerfectPrespectrumMap (polynomial.map g))
    (boundedFlatPerfectPrespectrumMap (polynomial.map g))
    (polynomialSquareHomotopy g)
      (polynomialSquareHomotopy g)

/-- The original left polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inl_spanMap :
    HomotopyPushout.inl _ _ ≫ spanMap g =
      boundedFlatPerfectPrespectrumMap (polynomial.map g) ≫
        HomotopyPushout.inl _ _ :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The original right polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inr_spanMap :
    HomotopyPushout.inr _ _ ≫ spanMap g =
      boundedFlatPerfectPrespectrumMap (polynomial.map g) ≫
        HomotopyPushout.inr _ _ :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- Every cylinder point retains the original pasted geometric comparison tracks. -/
lemma spanMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (spanMap g).map n
        (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Y))
          (boundedFlatPerfectPrespectrumMap (projection.app Y)) n (s, x)) =
      (HomotopyPushout.mapSquareHomotopy _ _ _ _ (boundedFlatPerfectPrespectrumMap g)
        (boundedFlatPerfectPrespectrumMap (polynomial.map g))
        (boundedFlatPerfectPrespectrumMap (polynomial.map g))
        (polynomialSquareHomotopy g)
          (polynomialSquareHomotopy g)).level n
          (s, x) := rfl

/-- The positive Laurent chart retains its actual geometric square. -/
def plusSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (plus.app Y) ≫
      boundedFlatPerfectPrespectrumMap (laurent.map g))
    (boundedFlatPerfectPrespectrumMap (polynomial.map g) ≫
      boundedFlatPerfectPrespectrumMap (plus.app X)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _
    (plus.naturality g)

/-- The inverse-coordinate Laurent chart retains its actual geometric square. -/
def minusSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (minus.app Y) ≫
      boundedFlatPerfectPrespectrumMap (laurent.map g))
    (boundedFlatPerfectPrespectrumMap (polynomial.map g) ≫
      boundedFlatPerfectPrespectrumMap (minus.app X)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _
    (minus.naturality g)

/-- The original outer Laurent projection square is common to both chart diagrams. -/
def laurentSquareHomotopy :=
  boundedFlatPerfectPrespectrumSquareHomotopy (laurent.map g)
    (laurentProjection.app Y) (laurentProjection.app X) g
      (laurentProjection.naturality g)

/-- Paste the original plus Laurent square and the original polynomial square. -/
def plusInputLeftTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquareHomotopy g).postcomp
      (boundedFlatPerfectPrespectrumMap (plus.app X)))

/-- The plus route through the common original Laurent projection square. -/
def plusInputRightTrack :=
  ((plusHomotopy Y).postcomp
    (boundedFlatPerfectPrespectrumMap (laurent.map g))).symm.trans
    ((laurentSquareHomotopy g).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
        (plusHomotopy X)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original plus scheme-arrow tracks and common outer square. -/
def plusInputPasting :
    (plusInputLeftTrack g).RelHomotopy
      (plusInputRightTrack g) :=
  DoubleSquareTrack.projectionComparison (projection.app Y) (plus.app Y)
    (projection.app X) (plus.app X) g
    (polynomial.map g) (laurent.map g)
    (projection.naturality g)
      (plus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (plus_projection Y) (plus_projection X)

/-- Paste the original minus Laurent square and the original polynomial square. -/
def minusInputLeftTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app Y))
    (minusSquareHomotopy g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquareHomotopy g).postcomp
      (boundedFlatPerfectPrespectrumMap (minus.app X)))

/-- The minus route through the common original Laurent projection square. -/
def minusInputRightTrack :=
  ((minusHomotopy Y).postcomp
    (boundedFlatPerfectPrespectrumMap (laurent.map g))).symm.trans
    ((laurentSquareHomotopy g).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
        (minusHomotopy X)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original minus scheme-arrow tracks and common outer square. -/
def minusInputPasting :
    (minusInputLeftTrack g).RelHomotopy
      (minusInputRightTrack g) :=
  DoubleSquareTrack.projectionComparison (projection.app Y) (minus.app Y)
    (projection.app X) (minus.app X) g
    (polynomial.map g) (laurent.map g)
    (projection.naturality g)
      (minus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (minus_projection Y) (minus_projection X)

end Quillen.PerfectComplexes.GlobalRawBass
