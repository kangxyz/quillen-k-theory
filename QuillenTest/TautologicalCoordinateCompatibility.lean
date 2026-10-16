/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoordinateCone
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalSections
public import QuillenTest.TautologicalFirstCoordinate
public import QuillenTest.TautologicalCoordinateCone

/-! Co-import the original sections owner and the new cone owner, retaining the exact arrow. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.TautologicalCoordinateCompatibility

/-- The new light projection is literally the repository's original tautological first arrow. -/
theorem first_projection_eq_original_first_coordinate (R : CommRingCat.{u}) :
    tautologicalInclusionFirstProjection R = tautologicalFirstCoordinate R := rfl

/-- The actual perfect-coordinate chain map uses that unchanged original first arrow. -/
theorem perfect_coordinate_uses_original_arrow (R : CommRingCat.{u}) :
    (tautologicalCoordinatePerfect R).hom =
      (CochainComplex.singleFunctor (twoChartLine R).Modules 0).map
        (tautologicalFirstCoordinate R) := rfl

/-- The actual signed supported cone is the literal mapping cone of the original coordinate. -/
theorem supported_cone_uses_original_arrow (R : CommRingCat.{u}) :
    (tautologicalCoordinateSupportedCone R).obj =
      CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (twoChartLine R).Modules 0).map
          (tautologicalFirstCoordinate R)) := rfl

/-- The old positive theorem retains its original postcomposition statement and owner. -/
theorem original_positive_coordinate_square (R : CommRingCat.{u}) :
    (Scheme.Modules.restrictFunctor (plusChart R)).map
        (tautologicalInclusionFirstProjection R) ≫
      (Scheme.Modules.restrictUnitIso (plusChart R)).hom =
        (tautologicalLinePlusIso R).hom := by
  rw [first_projection_eq_original_first_coordinate]
  exact tautologicalFirstCoordinate_plus R

end QuillenTest.TautologicalCoordinateCompatibility
