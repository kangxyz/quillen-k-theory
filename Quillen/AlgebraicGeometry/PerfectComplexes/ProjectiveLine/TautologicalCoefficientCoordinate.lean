/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorToUnitCharts
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison
public import Aglib.Algebra.Homology.MappingCone.Iso

/-!
# The original tautological coordinate with arbitrary perfect coefficients

Tensor the actual original first coordinate on the left of an arbitrary coefficient complex.
The actual positive restriction is the original line-tensor chart isomorphism; the negative
restriction is that same chart comparison followed by the original polynomial scalar.
The literal signed mapping cone is therefore supported away from the positive chart.
This supplies object geometry only, without a K-zero descent or all-degree operation.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Modules

/-- Left tensor of the actual original first coordinate on arbitrary complexes. -/
def tautologicalCoefficientCoordinate (R : CommRingCat.{u}) :
    AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R) ⟶ 𝟭
      (CochainComplex (twoChartLine R).Modules ℤ) :=
  AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit (tautologicalFirstCoordinate R)

/-- The actual positive restricted coordinate is the original line-tensor chart isomorphism. -/
theorem tautologicalCoefficientCoordinate_plus (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) :
    (restrict (plusChart R)).map ((tautologicalCoefficientCoordinate R).app K) =
      (tensorByLineComplexChartIso (plusChart R) (tautologicalLine R)
        (tautologicalLinePlusIso R)).hom.app K :=
  complexLineCoordinate_chart_iso (plusChart R) (tautologicalFirstCoordinate R)
    (tautologicalLinePlusIso R) (tautologicalFirstCoordinate_plus R) K

/-- The actual negative restricted coordinate is the original polynomial scalar. -/
theorem tautologicalCoefficientCoordinate_minus (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) :
    (restrict (minusChart R)).map ((tautologicalCoefficientCoordinate R).app K) =
      (tensorByLineComplexChartIso (minusChart R) (tautologicalLine R)
        (tautologicalLineMinusIso R)).hom.app K ≫
      (complexGlobalScalar _ (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialGlobalCoordinate
        R)).app
        ((restrict (minusChart R)).obj K) :=
  complexLineCoordinate_chart_scalar (minusChart R) (tautologicalFirstCoordinate R)
    (tautologicalLineMinusIso R) (polynomialCoordinate R)
    (tautologicalFirstCoordinate_minus R) K

/-- The original positive restricted coordinate is invertible for every coefficient complex. -/
instance tautologicalCoefficientCoordinate_plus_isIso (R : CommRingCat.{u})
    (K : CochainComplex (twoChartLine R).Modules ℤ) :
    IsIso ((restrict (plusChart R)).map ((tautologicalCoefficientCoordinate R).app K)) := by
  rw [tautologicalCoefficientCoordinate_plus]
  infer_instance

/-- The same coordinate in the original perfect tensor functor, with the actual two charts. -/
def tautologicalCoefficientPerfectCoordinate (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (perfectTensorByLine (tautologicalLine R)
      (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
      (polynomialChart_cover R) (fun b => by
        cases b
        · exact tautologicalLineMinusIso R
        · exact tautologicalLinePlusIso R)).obj K ⟶ K :=
  (locallyPerfect _).homMk ((tautologicalCoefficientCoordinate R).app K.obj)

/-- The perfect coordinate remains the literal original tensor coefficient chain map. -/
theorem tautologicalCoefficientPerfectCoordinate_original (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (tautologicalCoefficientPerfectCoordinate R K).hom =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit
        (tautologicalFirstCoordinate R)).app K.obj := rfl

/-- The original positive open localization sees the actual coefficient coordinate as weak. -/
theorem tautologicalCoefficientPerfectCoordinate_openWeak (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (perfectOpenWeakWaldhausen (plusChart R)).weq
      (tautologicalCoefficientPerfectCoordinate R K) := by
  rw [perfectOpenWeakWaldhausen_weq_iff]
  change QuasiIso ((restrict (plusChart R)).map
    ((tautologicalCoefficientCoordinate R).app K.obj))
  infer_instance

/-- The actual signed coordinate cone with arbitrary original perfect coefficients. -/
def tautologicalCoefficientSupportedCone (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (perfectSupported (plusChart R)).FullSubcategory :=
  ⟨CochainComplex.mappingCone (tautologicalCoefficientPerfectCoordinate R K).hom,
    perfectOpenWeak_mappingCone_supported (plusChart R)
      (tautologicalCoefficientPerfectCoordinate R K)
      (tautologicalCoefficientPerfectCoordinate_openWeak R K)⟩

/-- The literal negative cone is compared with the original scalar on the restricted coefficient. -/
def tautologicalCoefficientConeMinusIso (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (restrict (minusChart R)).obj (tautologicalCoefficientSupportedCone R K).obj ≅
      CochainComplex.mappingCone
        ((complexGlobalScalar _
          (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialGlobalCoordinate R)).app
            ((restrict (minusChart R)).obj K.obj)) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso
      (tautologicalCoefficientPerfectCoordinate R K).hom
      (Scheme.Modules.restrictFunctor (minusChart R)) ≪≫
    CochainComplex.mappingCone.isoOfIso _ _
      ((tensorByLineComplexChartIso (minusChart R) (tautologicalLine R)
        (tautologicalLineMinusIso R)).app K.obj) (Iso.refl _)
      (by
        change (restrict (minusChart R)).map
          ((tautologicalCoefficientCoordinate R).app K.obj) ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact tautologicalCoefficientCoordinate_minus R K.obj)

end Quillen.PerfectComplexes.ProjectiveLine
