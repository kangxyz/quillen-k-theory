/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassPasting
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Units
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining

/-! Actual Laurent-unit tracks commute relatively with the original coefficient square. -/
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


namespace LaurentUnitTrack
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original old-ring Laurent projection composition track. -/
def oldComposition :=
  boundedFlatPerfectPrespectrumCompHomotopy (Spec.map (laurentMap f)) (laurentProjection R)

/-- The original new-ring projection track with the genuine scheme-square endpoint transport. -/
def newComposition :=
  (boundedFlatPerfectPrespectrumCompHomotopy (laurentProjection S) (Spec.map f)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (laurentMap_projection f)).symm rfl

/-- The common genuine pulled-back unit loop at the original composite map. -/
def commonUnit :=
  boundedFlatPerfectUnitHomotopy (Spec.map (laurentMap f) ≫ laurentProjection R)
    (laurentGlobalUnit S)

/-- The original old-ring unit loop followed by Laurent coefficient change. -/
def oldUnit :=
  (boundedFlatLaurentUnitHomotopy R).postcomp
    (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))

/-- The original new-ring unit loop preceded by the base coefficient map. -/
def newUnit :=
  Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
    (boundedFlatLaurentUnitHomotopy S)

/-- Actual scalar transport supplies the old projection's full unit comparison. -/
def oldComparison :
    ((oldComposition f).trans (oldUnit f)).RelHomotopy
      ((commonUnit f).trans (oldComposition f)) := by
  have J := boundedFlatPerfectUnitTrackPostcomp (Spec.map (laurentMap f))
    (laurentProjection R) (laurentGlobalUnit R)
  simpa only [oldComposition, oldUnit, commonUnit, boundedFlatLaurentUnitHomotopy,
    laurentGlobalUnit_coefficient] using J

/-- Target scalar naturality supplies the new projection's full unit comparison. -/
def newComparison :
    ((newComposition f).trans (newUnit f)).RelHomotopy
      ((commonUnit f).trans (newComposition f)) := by
  refine (boundedFlatPerfectUnitTrackPrecomp (laurentProjection S) (Spec.map f)
    (laurentGlobalUnit S)).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr
    · exact congrArg (fun q ↦ (boundedFlatPerfectUnitHomotopy q
        (laurentGlobalUnit S)).level n) (laurentMap_projection f)
    · rfl

/-- The two original projection comparisons intertwine the two unchanged unit loops. -/
def squarePasting :
    ((oldUnit f).trans ((oldComposition f).symm.trans (newComposition f))).RelHomotopy
      (((oldComposition f).symm.trans (newComposition f)).trans (newUnit f)) :=
  Homotopy.RelHomotopy.intertwine _ _ _ _ _ (oldComparison f) (newComparison f)

end LaurentUnitTrack
end Quillen.PerfectComplexes
