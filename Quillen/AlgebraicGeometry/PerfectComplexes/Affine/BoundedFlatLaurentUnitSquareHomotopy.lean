/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatLaurentUnitTrack
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-! The actual moving Laurent-unit square under arbitrary coefficient change. -/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The existing exported Laurent coefficient square retains both exact original binary tracks. -/
lemma boundedFlatLaurentCoefficientSquareHomotopy_level (n : ℕ) :
    (boundedFlatLaurentCoefficientSquareHomotopy f).level n =
      ((LaurentUnitTrack.oldComposition f).symm.trans
        (LaurentUnitTrack.newComposition f)).level n :=
  boundedFlatPerfectPrespectrumSquareHomotopy_level (Spec.map (laurentMap f))
    (laurentProjection R) (laurentProjection S) (Spec.map f) (laurentMap_projection f) n

/-- The unchanged old and new unit loops intertwine across the exact original coefficient square. -/
def boundedFlatLaurentUnitCoefficientPasting :
    ((LaurentUnitTrack.oldUnit f).trans
      (boundedFlatLaurentCoefficientSquareHomotopy f)).RelHomotopy
    ((boundedFlatLaurentCoefficientSquareHomotopy f).trans (LaurentUnitTrack.newUnit f)) := by
  refine (LaurentUnitTrack.squarePasting f).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact boundedFlatLaurentCoefficientSquareHomotopy_level f n
  · intro n
    apply Homotopy.trans_level_congr
    · exact boundedFlatLaurentCoefficientSquareHomotopy_level f n
    · rfl

/-- The genuine unit comparison has the precise three-sided moving-square boundary. -/
def boundedFlatLaurentUnitCoefficientBoundary :
    (LaurentUnitTrack.oldUnit f).RelHomotopy
      (((boundedFlatLaurentCoefficientSquareHomotopy f).trans
        (LaurentUnitTrack.newUnit f)).trans
          (boundedFlatLaurentCoefficientSquareHomotopy f).symm) :=
  Homotopy.RelHomotopy.conjugateBoundary _ _ _ (boundedFlatLaurentUnitCoefficientPasting f)

/-- Every ring map yields a genuine moving square between the two original Laurent-unit loops. -/
def boundedFlatLaurentUnitCoefficientSquare :
    (LaurentUnitTrack.oldUnit f).Square (LaurentUnitTrack.newUnit f)
      (boundedFlatLaurentCoefficientSquareHomotopy f)
      (boundedFlatLaurentCoefficientSquareHomotopy f) :=
  (boundedFlatLaurentUnitCoefficientBoundary f).toSquare

/-- Every original relative comparison point survives the actual parameter-square quotient. -/
lemma boundedFlatLaurentUnitCoefficientSquare_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatLaurentUnitCoefficientSquare f).level n
      ((Quillen.ThreeSideSquare.collapse z).1,
        ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatLaurentUnitCoefficientBoundary f).level n (z.1, (z.2, x)) :=
  (boundedFlatLaurentUnitCoefficientBoundary f).toSquare_collapse n z x

end Quillen.PerfectComplexes
