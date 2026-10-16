/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientCoordinate
public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoordinateCone

/-!
# Exact rank-one compatibility of the coefficient coordinate cone

The original single/tensor comparison and right unitor identify the coefficient coordinate
at the actual rank-one perfect complex with the original single coordinate. The corresponding
literal signed cone comparison preserves the target inclusion and the same support predicate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine

/-- The original coefficient arrow at rank one is exactly the original single coordinate. -/
theorem tautologicalCoefficientCoordinate_rankOne (R : CommRingCat.{u}) :
    (tautologicalCoefficientPerfectCoordinate R (rankOnePerfect (twoChartLine R))).hom =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftSingleUnitIso (twoChartLine R)
        (tautologicalLine R) 0).hom ≫
        (tautologicalCoordinatePerfect R).hom :=
  AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit_single (tautologicalFirstCoordinate R) 0

/-- Actual rank-one cone comparison through the original coordinate square. -/
def tautologicalCoefficientRankOneConeIso (R : CommRingCat.{u}) :
    (tautologicalCoefficientSupportedCone R (rankOnePerfect (twoChartLine R))).obj ≅
      (tautologicalCoordinateSupportedCone R).obj :=
  CochainComplex.mappingCone.isoOfIso _ _
    (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftSingleUnitIso (twoChartLine R)
      (tautologicalLine R) 0) (Iso.refl _)
    (by
      change (tautologicalCoefficientPerfectCoordinate R (rankOnePerfect (twoChartLine R))).hom ≫
        𝟙 _ = _
      rw [Category.comp_id]
      exact tautologicalCoefficientCoordinate_rankOne R)

/-- The actual target cone inclusion is unchanged by the rank-one comparison. -/
theorem tautologicalCoefficientRankOneConeIso_inr (R : CommRingCat.{u}) :
    CochainComplex.mappingCone.inr
        (tautologicalCoefficientPerfectCoordinate R (rankOnePerfect (twoChartLine R))).hom ≫
      (tautologicalCoefficientRankOneConeIso R).hom =
        CochainComplex.mappingCone.inr (tautologicalCoordinatePerfect R).hom := by
  simp [tautologicalCoefficientRankOneConeIso, CochainComplex.mappingCone.isoOfIso,
    CochainComplex.mappingCone.map]

/-- The same literal positive-chart support predicate contains the exact cone comparison. -/
def tautologicalCoefficientRankOneSupportedIso (R : CommRingCat.{u}) :
    tautologicalCoefficientSupportedCone R (rankOnePerfect (twoChartLine R)) ≅
      tautologicalCoordinateSupportedCone R :=
  (perfectSupported (plusChart R)).isoMk (tautologicalCoefficientRankOneConeIso R)

/-- The actual coefficient cone at rank one has the already fixed original supported class. -/
theorem tautologicalCoefficientRankOneSupported_class (R : CommRingCat.{u}) :
    (perfectSupportedWaldhausen (plusChart R)).kZeroObjectClass
        (tautologicalCoefficientSupportedCone R (rankOnePerfect (twoChartLine R))) =
      (perfectSupportedWaldhausen (plusChart R)).kZeroObjectClass
        (tautologicalCoordinateSupportedCone R) :=
  (perfectSupportedWaldhausen (plusChart R)).kZeroObjectClass_iso
    (tautologicalCoefficientRankOneSupportedIso R)

end Quillen.PerfectComplexes.ProjectiveLine
