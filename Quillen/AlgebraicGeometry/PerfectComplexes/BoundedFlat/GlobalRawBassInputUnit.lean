/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining

/-!
# Forward Laurent units across the original global raw input square

The actual forward Laurent coordinate is preserved by geometric pullback. Its original unit
homotopies intertwine with the entire original split Laurent projection square.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every actual scheme map preserves the original pulled-back forward Laurent coordinate. -/
theorem laurentUnit_map :
    Units.map (laurent.map g).appTop.hom.toMonoidHom
      (GlobalSchemeLaurentTrack.laurentScalar (op Y)) =
      GlobalSchemeLaurentTrack.laurentScalar (op X) :=
  GlobalSchemeLaurentTrack.laurentScalar_map g.op

namespace InputUnit

/-- The original source-fiber Laurent projection composition track. -/
def oldComposition :=
  boundedFlatPerfectPrespectrumCompHomotopy
    (laurent.map g) (laurentProjection.app Y)

/-- The original target-fiber track with its genuine scheme-arrow-square endpoint transport. -/
def newComposition :=
  (boundedFlatPerfectPrespectrumCompHomotopy (laurentProjection.app X)
    g).cast
    (congrArg boundedFlatPerfectPrespectrumMap
      (laurentProjection.naturality g)).symm rfl

/-- The common actual pulled-back forward unit on the original composite map. -/
def commonUnit :=
  boundedFlatPerfectUnitHomotopy
    (laurent.map g ≫ laurentProjection.app Y)
    (GlobalSchemeLaurentTrack.laurentScalar (op X))

/-- The original old unit loop followed by the actual Laurent scheme-arrow map. -/
def oldUnit :=
  (unitHomotopy Y).postcomp
    (boundedFlatPerfectPrespectrumMap (laurent.map g))

/-- The original target unit loop preceded by the actual base scheme-arrow map. -/
def newUnit :=
  Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
    (unitHomotopy X)

/-- Exact scalar transport preserves the entire old projection-unit comparison. -/
def oldComparison :
    ((oldComposition g).trans (oldUnit g)).RelHomotopy
      ((commonUnit g).trans (oldComposition g)) := by
  have J := boundedFlatPerfectUnitTrackPostcomp
    (laurent.map g) (laurentProjection.app Y)
    (GlobalSchemeLaurentTrack.laurentScalar (op Y))
  simpa only [oldComposition, oldUnit, commonUnit, unitHomotopy,
    laurentUnit_map] using J

/-- The new projection-unit comparison keeps the actual scheme-square transport. -/
def newComparison :
    ((newComposition g).trans (newUnit g)).RelHomotopy
      ((commonUnit g).trans (newComposition g)) := by
  refine (boundedFlatPerfectUnitTrackPrecomp (laurentProjection.app X) g
    (GlobalSchemeLaurentTrack.laurentScalar (op X))).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr
    · exact congrArg (fun q ↦ (boundedFlatPerfectUnitHomotopy q
        (GlobalSchemeLaurentTrack.laurentScalar (op X))).level n)
        (laurentProjection.naturality g)
    · rfl

/-- The two specified projection comparisons intertwine the unchanged forward unit loops. -/
def squarePasting :
    ((oldUnit g).trans ((oldComposition g).symm.trans (newComposition g))).RelHomotopy
      (((oldComposition g).symm.trans (newComposition g)).trans (newUnit g)) :=
  Homotopy.RelHomotopy.intertwine _ _ _ _ _ (oldComparison g) (newComparison g)

end InputUnit

/-- The existing outer Laurent square retains both complete original composition tracks. -/
theorem laurentSquareHomotopy_level (n : ℕ) :
    (laurentSquareHomotopy g).level n =
      ((InputUnit.oldComposition g).symm.trans
        (InputUnit.newComposition g)).level n :=
  boundedFlatPerfectPrespectrumSquareHomotopy_level
    (laurent.map g) (laurentProjection.app Y)
    (laurentProjection.app X) g
    (laurentProjection.naturality g) n

/-- The original forward-unit loops intertwine across the whole actual Laurent square. -/
def laurentUnitPasting :
    ((InputUnit.oldUnit g).trans
      (laurentSquareHomotopy g)).RelHomotopy
    ((laurentSquareHomotopy g).trans
      (InputUnit.newUnit g)) := by
  refine (InputUnit.squarePasting g).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact laurentSquareHomotopy_level g n
  · intro n
    apply Homotopy.trans_level_congr
    · exact laurentSquareHomotopy_level g n
    · rfl

end Quillen.PerfectComplexes.GlobalRawBass
