/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeCoordinate
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassCharts
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorToUnitCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison
public import Quillen.Aglib.Algebra.Homology.MappingCone.Iso
/-!
# Native coefficient coordinate cones

The actual global first coordinate is tensored with an arbitrary perfect complex. Its literal
signed cone is supported off the original positive native range. The actual negative-chart
restriction is isomorphic to the polynomial scalar cone on the same coefficient complex.
The K-class formula and its identification with the terminal boundary remain open.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

variable (X : QuasiCompactSchemes.{u})

/-- Tensor the original native first coordinate with the unchanged coefficient complex. -/
def coefficientCoordinate :
    Scheme.Modules.Complex.tensorLeft (nativeTautologicalLine X) ⟶
      𝟭 (CochainComplex (nativeLineFunctor.obj X).obj.Modules ℤ) :=
  Scheme.Modules.Complex.tensorToUnit (nativeFirstCoordinate X)

/-- The positive coordinate is exactly the native line-tensor chart isomorphism. -/
theorem coefficientCoordinate_plus (K : CochainComplex (nativeLineFunctor.obj X).obj.Modules ℤ) :
    (restrict (nativePlus.app X).hom).map ((coefficientCoordinate X).app K) =
      (tensorByLineComplexChartIso (nativePlus.app X).hom (nativeTautologicalLine X)
        (nativeTautologicalPlusIso X)).hom.app K :=
  complexLineCoordinate_chart_iso _ (nativeFirstCoordinate X)
    (nativeTautologicalPlusIso X) (nativeFirstCoordinate_plus X) K

/-- The negative coordinate is exactly the original native polynomial scalar. -/
theorem coefficientCoordinate_minus (K : CochainComplex (nativeLineFunctor.obj X).obj.Modules ℤ) :
    (restrict (nativeMinus.app X).hom).map ((coefficientCoordinate X).app K) =
      (tensorByLineComplexChartIso (nativeMinus.app X).hom (nativeTautologicalLine X)
        (nativeTautologicalMinusIso X)).hom.app K ≫
      (complexGlobalScalar _ (nativePolynomialCoordinate X)).app
        ((restrict (nativeMinus.app X).hom).obj K) :=
  complexLineCoordinate_chart_scalar _ (nativeFirstCoordinate X)
    (nativeTautologicalMinusIso X) (nativePolynomialCoordinate X)
    (nativeFirstCoordinate_minus X) K

instance coefficientCoordinate_plus_isIso
    (K : CochainComplex (nativeLineFunctor.obj X).obj.Modules ℤ) :
    IsIso ((restrict (nativePlus.app X).hom).map ((coefficientCoordinate X).app K)) := by
  rw [coefficientCoordinate_plus]
  infer_instance

/-- The actual coordinate in the original native perfect negative-twist functor. -/
def coefficientPerfectCoordinate (K : Perfect (nativeLineFunctor.obj X).obj) :
    (nativeNegativeTwist X).obj K ⟶ K :=
  (locallyPerfect _).homMk ((coefficientCoordinate X).app K.obj)

/-- The original positive native chart sees the coordinate as a weak equivalence. -/
theorem coefficientPerfectCoordinate_openWeak (K : Perfect (nativeLineFunctor.obj X).obj) :
    (perfectOpenWeakWaldhausen (nativePlus.app X).hom).weq
      (coefficientPerfectCoordinate X K) := by
  rw [perfectOpenWeakWaldhausen_weq_iff]
  change QuasiIso ((restrict (nativePlus.app X).hom).map
    ((coefficientCoordinate X).app K.obj))
  infer_instance

/-- The literal signed cone, first with support recorded on the original positive chart. -/
def coefficientChartCone (K : Perfect (nativeLineFunctor.obj X).obj) :
    (perfectSupported (nativePlus.app X).hom).FullSubcategory :=
  ⟨CochainComplex.mappingCone (coefficientPerfectCoordinate X K).hom,
    perfectOpenWeak_mappingCone_supported _ (coefficientPerfectCoordinate X K)
      (coefficientPerfectCoordinate_openWeak X K)⟩

/-- The inverse original chart isomorphism retains the actual positive range inclusion. -/
@[reassoc]
theorem positiveOpenIso_inv_plus :
    (positiveOpenIso X).inv ≫ (nativePlus.app X).hom = (positiveOpen X).ι := by
  rw [← positiveOpenIso_hom_inclusion, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The same cone on the positive range is the actual inverse-isomorphism restriction. -/
def coefficientConePositiveIso (K : Perfect (nativeLineFunctor.obj X).obj) :
    (restrict (positiveOpen X).ι).obj (coefficientChartCone X K).obj ≅
      (restrict (positiveOpenIso X).inv).obj
        ((restrict (nativePlus.app X).hom).obj (coefficientChartCone X K).obj) :=
  (eqToIso (restrict_congr (positiveOpenIso_inv_plus X).symm)).app _ ≪≫
    (restrictCompIso (positiveOpenIso X).inv (nativePlus.app X).hom).symm.app _

/-- The identical signed cone supported off the literal native positive range open. -/
def coefficientSupportedCone (K : Perfect (nativeLineFunctor.obj X).obj) :
    (perfectSupported (positiveOpen X).ι).FullSubcategory :=
  ⟨(coefficientChartCone X K).obj, (coefficientChartCone X K).property.1,
    fun n => (acyclic_restrict (positiveOpenIso X).inv
      (coefficientChartCone X K).property.2 n).of_iso
        (coefficientConePositiveIso X K).symm⟩

/-- Actual negative restriction is the polynomial scalar cone on the same coefficient. -/
def coefficientConeMinusIso (K : Perfect (nativeLineFunctor.obj X).obj) :
    (restrict (nativeMinus.app X).hom).obj (coefficientSupportedCone X K).obj ≅
      CochainComplex.mappingCone
        ((complexGlobalScalar _ (nativePolynomialCoordinate X)).app
          ((restrict (nativeMinus.app X).hom).obj K.obj)) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso
      (coefficientPerfectCoordinate X K).hom
      (Scheme.Modules.restrictFunctor (nativeMinus.app X).hom) ≪≫
    CochainComplex.mappingCone.isoOfIso _ _
      ((tensorByLineComplexChartIso (nativeMinus.app X).hom (nativeTautologicalLine X)
        (nativeTautologicalMinusIso X)).app K.obj) (Iso.refl _)
      (by
        change (restrict (nativeMinus.app X).hom).map
          ((coefficientCoordinate X).app K.obj) ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact coefficientCoordinate_minus X K.obj)

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
