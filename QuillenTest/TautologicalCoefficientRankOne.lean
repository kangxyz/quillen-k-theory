/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientRankOne
public import QuillenTest.LineCoordinateSingle
public import QuillenTest.TautologicalCoefficientCoordinate

/-! Actual rank-one chain, cone inclusion and supported class alignment. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine
namespace QuillenTest.TautologicalCoefficientRankOne

/-- The inverse single/tensor comparison recovers the original first-coordinate chain map. -/
theorem original_rank_one_chain_map (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftSingleUnitIso (twoChartLine R)
      (tautologicalLine R) 0).inv ≫
        (tautologicalCoefficientPerfectCoordinate R (rankOnePerfect (twoChartLine R))).hom =
      (tautologicalCoordinatePerfect R).hom := by
  rw [tautologicalCoefficientCoordinate_rankOne]
  simp

/-- The literal original cone inclusion agrees through the actual rank-one comparison. -/
theorem original_rank_one_cone_inclusion (R : CommRingCat.{u}) :
    CochainComplex.mappingCone.inr
        (tautologicalCoefficientPerfectCoordinate R (rankOnePerfect (twoChartLine R))).hom ≫
      (tautologicalCoefficientRankOneConeIso R).hom =
        CochainComplex.mappingCone.inr (tautologicalCoordinatePerfect R).hom :=
  tautologicalCoefficientRankOneConeIso_inr R

/-- The original supported class comparison also retains the zero ring. -/
theorem zero_ring_original_supported_class :
    (perfectSupportedWaldhausen (plusChart (.of (ZMod 1)))).kZeroObjectClass
        (tautologicalCoefficientSupportedCone (.of (ZMod 1))
          (rankOnePerfect (twoChartLine (.of (ZMod 1))))) =
      (perfectSupportedWaldhausen (plusChart (.of (ZMod 1)))).kZeroObjectClass
        (tautologicalCoordinateSupportedCone (.of (ZMod 1))) :=
  tautologicalCoefficientRankOneSupported_class _

end QuillenTest.TautologicalCoefficientRankOne
