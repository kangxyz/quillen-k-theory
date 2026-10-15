/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.PolynomialLaurent
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.BaseChangeGluing
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The original projective line over an arbitrary quasi-compact scheme

Base change the actual integer two-chart line. The chart sources and overlap maps
are literally the native Bass polynomial and Laurent products. The original
tautological subline is pulled back along the actual second projection.
No projective-bundle formula or projection-perfectness premise is used.
-/
@[expose] public section
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Bass
open AlgebraicGeometry.Scheme.Modules

instance integerProjection_quasiCompact : QuasiCompact (projection integerRing.{u}) := by
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

/-- The genuine native product with the original integer projective line. -/
def nativeLineFunctor : QuasiCompactSchemes.{u} ⥤ QuasiCompactSchemes.{u} :=
  qcBaseProductFunctor (projection integerRing)

/-- The original relative projection, with all base arrows unrestricted. -/
def nativeProjection : nativeLineFunctor.{u} ⟶ 𝟭 _ where
  app X := ⟨(baseProductProjection (projection integerRing)).app X.obj⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (baseProductProjection _).naturality f.hom

/-- The positive chart has exactly the original native polynomial source. -/
def nativePlus : polynomialFunctor.{u} ⟶ nativeLineFunctor :=
  qcBaseProductTransformation _ _ (plusChart integerRing) (plusChart_projection integerRing)

/-- The inverse-coordinate chart has exactly the same original polynomial source. -/
def nativeMinus : polynomialFunctor.{u} ⟶ nativeLineFunctor :=
  qcBaseProductTransformation _ _ (minusChart integerRing) (minusChart_projection integerRing)

/-- The actual second projection to the fixed original integer line. -/
def nativeIntegerProjection (X : QuasiCompactSchemes.{u}) :
    (nativeLineFunctor.obj X).obj ⟶ twoChartLine integerRing :=
  pullback.snd _ _

instance nativePlus_isOpenImmersion (X : QuasiCompactSchemes.{u}) :
    IsOpenImmersion (nativePlus.app X).hom :=
  instIsOpenImmersionBaseProductTransformation _ _ _ (plusChart_projection integerRing) X.obj

instance nativeMinus_isOpenImmersion (X : QuasiCompactSchemes.{u}) :
    IsOpenImmersion (nativeMinus.app X).hom :=
  instIsOpenImmersionBaseProductTransformation _ _ _ (minusChart_projection integerRing) X.obj

instance nativeProjection_flat (X : QuasiCompactSchemes.{u}) :
    Flat (nativeProjection.app X).hom := by
  change Flat (pullback.fst (toIntegerBase X.obj) (projection integerRing))
  infer_instance

instance nativeLine_quasiSeparated (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] :
    QuasiSeparatedSpace (nativeLineFunctor.obj X).obj := by
  change QuasiSeparatedSpace (pullback (toIntegerBase X.obj) (projection integerRing) : Scheme)
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (toIntegerBase X.obj) (projection integerRing))

/-- The positive chart retains the native polynomial structural map. -/
@[reassoc (attr := simp)]
theorem nativePlus_projection (X : QuasiCompactSchemes.{u}) :
    nativePlus.app X ≫ nativeProjection.app X = polynomialProjection.app X := by
  apply ObjectProperty.hom_ext
  exact baseProductTransformation_projection _ _ _ (plusChart_projection integerRing) X.obj

/-- The negative chart retains the native polynomial structural map. -/
@[reassoc (attr := simp)]
theorem nativeMinus_projection (X : QuasiCompactSchemes.{u}) :
    nativeMinus.app X ≫ nativeProjection.app X = polynomialProjection.app X := by
  apply ObjectProperty.hom_ext
  exact baseProductTransformation_projection _ _ _ (minusChart_projection integerRing) X.obj

/-- The overlap equation uses the original forward and inverse Laurent maps. -/
theorem native_overlap (X : QuasiCompactSchemes.{u}) :
    Bass.plus.app X ≫ nativePlus.app X = Bass.minus.app X ≫ nativeMinus.app X := by
  apply ObjectProperty.hom_ext
  apply pullback.hom_ext
  · simp [Bass.plus, Bass.minus, nativePlus, nativeMinus,
      qcBaseProductTransformation, baseProductTransformation]
  · simp [Bass.plus, Bass.minus, nativePlus, nativeMinus,
      qcBaseProductTransformation, baseProductTransformation, pullback.map,
      Category.assoc, overlap_equation]

/-- The actual positive chart is the inverse image of the original integer chart. -/
theorem nativePlus_isPullback (X : QuasiCompactSchemes.{u}) :
    IsPullback (nativePlus.app X).hom
      (pullback.snd (toIntegerBase X.obj) (PolynomialLaurent.polynomialProjection integerRing))
      (nativeIntegerProjection X) (plusChart integerRing) :=
  baseProductTransformation_isPullback _ _ _ (plusChart_projection integerRing) X.obj

/-- The actual negative chart is the inverse image of the original integer chart. -/
theorem nativeMinus_isPullback (X : QuasiCompactSchemes.{u}) :
    IsPullback (nativeMinus.app X).hom
      (pullback.snd (toIntegerBase X.obj) (PolynomialLaurent.polynomialProjection integerRing))
      (nativeIntegerProjection X) (minusChart integerRing) :=
  baseProductTransformation_isPullback _ _ _ (minusChart_projection integerRing) X.obj

/-- Both original native charts cover the native projective line. -/
theorem native_charts_cover (X : QuasiCompactSchemes.{u})
    (x : (nativeLineFunctor.obj X).obj) :
    (∃ y, (nativePlus.app X).hom y = x) ∨ (∃ y, (nativeMinus.app X).hom y = x) := by
  rcases charts_jointly_surjective integerRing (nativeIntegerProjection X x) with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (nativePlus_isPullback X)
      x y hy.symm
    exact Or.inl ⟨z, hz⟩
  · obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (nativeMinus_isPullback X)
      x y hy.symm
    exact Or.inr ⟨z, hz⟩

/-- The original actual tautological line over the native projective line. -/
def nativeTautologicalLine (X : QuasiCompactSchemes.{u}) :
    (nativeLineFunctor.obj X).obj.Modules :=
  (Scheme.Modules.pullback (nativeIntegerProjection X)).obj (tautologicalLine integerRing)

instance nativeTautologicalLine_finiteLocallyFree (X : QuasiCompactSchemes.{u}) :
    IsFiniteLocallyFree (nativeLineFunctor.obj X).obj (nativeTautologicalLine X) := by
  unfold nativeTautologicalLine
  infer_instance

/-- Restricting a pulled-back module along an actual commuting chart square. -/
def nativeModuleChartIso {W X Y Z : Scheme.{u}} (j : W ⟶ X) (q : X ⟶ Z)
    (a : W ⟶ Y) (i : Y ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion i]
    (h : j ≫ q = a ≫ i) (L : Z.Modules) :
    ((Scheme.Modules.pullback q).obj L).restrict j ≅
      (Scheme.Modules.pullback a).obj (L.restrict i) :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
    (Scheme.Modules.pullbackComp j q).app L ≪≫
    (Scheme.Modules.pullbackCongr h).app L ≪≫
    (Scheme.Modules.pullbackComp a i).symm.app L ≪≫
    (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.restrictFunctorIsoPullback i).symm.app L)

/-- Positive trivialization of the actual native negative line. -/
def nativeTautologicalPlusIso (X : QuasiCompactSchemes.{u}) :
    (nativeTautologicalLine X).restrict (nativePlus.app X).hom ≅
      SheafOfModules.unit (polynomialFunctor.obj X).obj.ringCatSheaf :=
  nativeModuleChartIso _ _ _ _ (nativePlus_isPullback X).w (tautologicalLine integerRing) ≪≫
    (Scheme.Modules.pullback _).mapIso (tautologicalLinePlusIso integerRing) ≪≫
    pullbackUnitIso _

/-- Negative trivialization of the same actual native negative line. -/
def nativeTautologicalMinusIso (X : QuasiCompactSchemes.{u}) :
    (nativeTautologicalLine X).restrict (nativeMinus.app X).hom ≅
      SheafOfModules.unit (polynomialFunctor.obj X).obj.ringCatSheaf :=
  nativeModuleChartIso _ _ _ _ (nativeMinus_isPullback X).w (tautologicalLine integerRing) ≪≫
    (Scheme.Modules.pullback _).mapIso (tautologicalLineMinusIso integerRing) ≪≫
    pullbackUnitIso _

end AlgebraicGeometry.Scheme.ProjectiveLine
