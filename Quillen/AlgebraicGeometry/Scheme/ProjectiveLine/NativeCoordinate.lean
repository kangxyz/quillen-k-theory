/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Native
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalSections
public import Quillen.Aglib.AlgebraicGeometry.Modules.RankOne.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
/-!
# The original tautological coordinate on a native projective line

Pull back the actual integer tautological coordinate along the original second projection.
The original native chart comparisons carry it to the identity on the positive chart and
the pulled-back polynomial coordinate on the negative chart. No affine detection principle,
projective-bundle formula or flatness of the base over the integers is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.Modules

variable {W X Y Z : Scheme.{u}} (j : W ⟶ X) (q : X ⟶ Z)
  (a : W ⟶ Y) (i : Y ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion i]
  (h : j ≫ q = a ≫ i)

/-- The actual native chart comparison is natural in the original module morphism. -/
@[reassoc]
theorem nativeModuleChartIso_naturality {M N : Z.Modules} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pullback q).map f) ≫
        (nativeModuleChartIso j q a i h N).hom =
      (nativeModuleChartIso j q a i h M).hom ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.restrictFunctor i).map f) := by
  let e := Functor.isoWhiskerLeft (Scheme.Modules.pullback q)
      (Scheme.Modules.restrictFunctorIsoPullback j) ≪≫
    Scheme.Modules.pullbackComp j q ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp a i).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback i).symm
      (Scheme.Modules.pullback a)
  exact e.hom.naturality f

/-- The actual chart comparison retains the canonical structure-module trivializations. -/
@[reassoc]
theorem nativeModuleChartIso_unit :
    (nativeModuleChartIso j q a i h (SheafOfModules.unit Z.ringCatSheaf)).hom ≫
        (Scheme.Modules.pullback a).map (Scheme.Modules.restrictUnitIso i).hom ≫
        (pullbackUnitIso a).hom =
      (Scheme.Modules.restrictFunctor j).map (pullbackUnitIso q).hom ≫
        (Scheme.Modules.restrictUnitIso j).hom := by
  have hi :
      (Scheme.Modules.pullback a).map
          ((Scheme.Modules.restrictFunctorIsoPullback i).inv.app
            (SheafOfModules.unit Z.ringCatSheaf)) ≫
          (Scheme.Modules.pullback a).map (Scheme.Modules.restrictUnitIso i).hom =
        (Scheme.Modules.pullback a).map (pullbackUnitIso i).hom := by
    rw [← Functor.map_comp, ← restrictFunctorIsoPullback_unit i,
      Iso.inv_hom_id_app_assoc]
  simp only [nativeModuleChartIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% hi, ← pullbackUnitIso_comp a i, Iso.inv_hom_id_app_assoc,
    pullbackUnitIso_congr, pullbackUnitIso_comp]
  rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality,
    Category.assoc, restrictFunctorIsoPullback_unit]

/-- The actual global first coordinate on the original native tautological line. -/
def nativeFirstCoordinate (X : QuasiCompactSchemes.{u}) :
    nativeTautologicalLine X ⟶
      SheafOfModules.unit (nativeLineFunctor.obj X).obj.ringCatSheaf :=
  (Scheme.Modules.pullback (nativeIntegerProjection X)).map
      (tautologicalFirstCoordinate integerRing) ≫
    (pullbackUnitIso (nativeIntegerProjection X)).hom

/-- The original polynomial coordinate pulled back to the native polynomial product. -/
def nativePolynomialCoordinate (X : QuasiCompactSchemes.{u}) :
    Γ((polynomialFunctor.obj X).obj, ⊤) :=
  (pullback.snd (toIntegerBase X.obj)
    (PolynomialLaurent.polynomialProjection integerRing)).appTop.hom
      (polynomialCoordinate integerRing)

/-- The positive restriction is the actual chosen native tautological trivialization. -/
theorem nativeFirstCoordinate_plus (X : QuasiCompactSchemes.{u}) :
    (Scheme.Modules.restrictFunctor (nativePlus.app X).hom).map (nativeFirstCoordinate X) ≫
      (Scheme.Modules.restrictUnitIso (nativePlus.app X).hom).hom =
        (nativeTautologicalPlusIso X).hom := by
  unfold nativeFirstCoordinate
  rw [Functor.map_comp, Category.assoc,
    ← nativeModuleChartIso_unit _ _ _ _ (nativePlus_isPullback X).w,
    ← Category.assoc, nativeModuleChartIso_naturality, Category.assoc,
    ← Functor.map_comp_assoc, tautologicalFirstCoordinate_plus]
  rfl

/-- The negative restriction is the original native trivialization followed by its coordinate. -/
theorem nativeFirstCoordinate_minus (X : QuasiCompactSchemes.{u}) :
    (Scheme.Modules.restrictFunctor (nativeMinus.app X).hom).map (nativeFirstCoordinate X) ≫
      (Scheme.Modules.restrictUnitIso (nativeMinus.app X).hom).hom =
        (nativeTautologicalMinusIso X).hom ≫
          unitMul _ (nativePolynomialCoordinate X) := by
  unfold nativeFirstCoordinate
  rw [Functor.map_comp, Category.assoc,
    ← nativeModuleChartIso_unit _ _ _ _ (nativeMinus_isPullback X).w,
    ← Category.assoc, nativeModuleChartIso_naturality, Category.assoc,
    ← Functor.map_comp_assoc, tautologicalFirstCoordinate_minus,
    Functor.map_comp, Category.assoc, unitMul_pullback]
  rfl

end AlgebraicGeometry.Scheme.ProjectiveLine
