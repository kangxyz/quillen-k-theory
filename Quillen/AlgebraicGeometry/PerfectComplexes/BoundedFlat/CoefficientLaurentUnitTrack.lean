/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMap
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining

/-! Actual coefficient-pulled forward Laurent units on arbitrary native fibers commute
relatively with the original geometric coefficient square. All original composition
tracks and normalization parameters are retained; no naturality data is supplied. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.PolynomialLaurent
  CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The actual native coefficient map preserves the pulled-back forward Laurent unit. -/
theorem boundedFlatCoefficientLaurentUnit_coefficient :
    Units.map (coefficientMap P ((laurentUnderFunctor R).map u)).appTop.hom.toMonoidHom
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (laurentGlobalUnit a.right)) =
      boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (laurentGlobalUnit b.right) := by
  have hr : Units.map (Spec.map ((laurentUnderFunctor R).map u).right).appTop.hom.toMonoidHom
      (laurentGlobalUnit a.right) = laurentGlobalUnit b.right :=
    laurentGlobalUnit_coefficient u.right
  simpa only [coefficientMap, hr] using
    boundedFlatCoefficientUnit_map
      (i := (op P, (laurentUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj b))
      (𝟙 (op P), (laurentUnderFunctor R).map u) (laurentGlobalUnit a.right)

namespace CoefficientLaurentUnitTrack

/-- The original source-fiber Laurent projection composition track. -/
def oldComposition :=
  boundedFlatPerfectPrespectrumCompHomotopy
    (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)

/-- The original target-fiber track with its genuine coefficient-square endpoint transport. -/
def newComposition :=
  (boundedFlatPerfectPrespectrumCompHomotopy (laurentProjection P b)
    (coefficientMap P u)).cast
    (congrArg boundedFlatPerfectPrespectrumMap
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (laurentUnderCoefficient R) u)).symm rfl

/-- The common actual pulled-back forward unit on the original composite map. -/
def commonUnit :=
  boundedFlatPerfectUnitHomotopy
    (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
      (laurentGlobalUnit b.right))

/-- The original old unit loop followed by the actual Laurent coefficient map. -/
def oldUnit :=
  (boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))

/-- The original target unit loop preceded by the actual base coefficient map. -/
def newUnit :=
  Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    (boundedFlatCoefficientLaurentUnitHomotopy P b)

/-- Exact scalar transport preserves the entire old projection-unit comparison. -/
def oldComparison :
    ((oldComposition P u).trans (oldUnit P u)).RelHomotopy
      ((commonUnit P u).trans (oldComposition P u)) := by
  have J := boundedFlatPerfectUnitTrackPostcomp
    (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (laurentGlobalUnit a.right))
  simpa only [oldComposition, oldUnit, commonUnit, boundedFlatCoefficientLaurentUnitHomotopy,
    boundedFlatCoefficientLaurentUnit_coefficient] using J

/-- The new projection-unit comparison keeps the actual scheme-square transport. -/
def newComparison :
    ((newComposition P u).trans (newUnit P u)).RelHomotopy
      ((commonUnit P u).trans (newComposition P u)) := by
  refine (boundedFlatPerfectUnitTrackPrecomp (laurentProjection P b) (coefficientMap P u)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
      (laurentGlobalUnit b.right))).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr
    · exact congrArg (fun q ↦ (boundedFlatPerfectUnitHomotopy q
        (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
          (laurentGlobalUnit b.right))).level n)
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
          (laurentUnderCoefficient R) u)
    · rfl

/-- The two specified projection comparisons intertwine the unchanged forward unit loops. -/
def squarePasting :
    ((oldUnit P u).trans ((oldComposition P u).symm.trans (newComposition P u))).RelHomotopy
      (((oldComposition P u).symm.trans (newComposition P u)).trans (newUnit P u)) :=
  Homotopy.RelHomotopy.intertwine _ _ _ _ _ (oldComparison P u) (newComparison P u)

end CoefficientLaurentUnitTrack

/-- The existing outer Laurent square retains both complete original composition tracks. -/
theorem boundedFlatCoefficientLaurentSquareHomotopy_level (n : ℕ) :
    (boundedFlatCoefficientLaurentSquareHomotopy P u).level n =
      ((CoefficientLaurentUnitTrack.oldComposition P u).symm.trans
        (CoefficientLaurentUnitTrack.newComposition P u)).level n :=
  boundedFlatPerfectPrespectrumSquareHomotopy_level
    (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)
    (laurentProjection P b) (coefficientMap P u)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (laurentUnderCoefficient R) u) n

/-- The original forward-unit loops intertwine across the whole actual Laurent square. -/
def boundedFlatCoefficientLaurentUnitPasting :
    ((CoefficientLaurentUnitTrack.oldUnit P u).trans
      (boundedFlatCoefficientLaurentSquareHomotopy P u)).RelHomotopy
    ((boundedFlatCoefficientLaurentSquareHomotopy P u).trans
      (CoefficientLaurentUnitTrack.newUnit P u)) := by
  refine (CoefficientLaurentUnitTrack.squarePasting P u).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact boundedFlatCoefficientLaurentSquareHomotopy_level P u n
  · intro n
    apply Homotopy.trans_level_congr
    · exact boundedFlatCoefficientLaurentSquareHomotopy_level P u n
    · rfl

end Quillen.PerfectComplexes
