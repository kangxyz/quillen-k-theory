/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Native
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurentBaseChange

/-! # Actual native overlap and affine projective-line comparison

The common-integer product has the original native Laurent intersection. Over
Spec R its canonical isomorphism with the existing twoChartLine R retains the
projection and both original polynomial charts. No base flatness is assumed.
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

/-- Every native base arrow gives the genuine cartesian projective-line square. -/
theorem nativeMap_isPullback {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y) :
    IsPullback (nativeLineFunctor.map f).hom (nativeProjection.app X).hom
      (nativeProjection.app Y).hom f.hom := by
  apply IsPullback.of_right (h₁₂ := nativeIntegerProjection Y) (h₂₂ := toIntegerBase Y.obj)
  · simpa [nativeLineFunctor, qcBaseProductFunctor, baseProductFunctor,
      nativeIntegerProjection, nativeProjection, baseProductProjection] using
      (IsPullback.of_hasPullback (toIntegerBase X.obj) (projection integerRing)).flip
  · exact congrArg (fun g => g.hom) (nativeProjection.naturality f)
  · exact (IsPullback.of_hasPullback (toIntegerBase Y.obj) (projection integerRing)).flip

instance nativeMap_isOpenImmersion {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f.hom] : IsOpenImmersion (nativeLineFunctor.map f).hom :=
  MorphismProperty.of_isPullback (nativeMap_isPullback f).flip inferInstance

instance nativePlus_isAffineHom (X : QuasiCompactSchemes.{u}) :
    IsAffineHom (nativePlus.app X).hom :=
  MorphismProperty.of_isPullback (nativePlus_isPullback X).flip inferInstance

instance nativeMinus_isAffineHom (X : QuasiCompactSchemes.{u}) :
    IsAffineHom (nativeMinus.app X).hom :=
  MorphismProperty.of_isPullback (nativeMinus_isPullback X).flip inferInstance

/-- The intersection of the two native charts is the original native Laurent scheme. -/
theorem native_chart_isPullback (X : QuasiCompactSchemes.{u}) :
    IsPullback (Bass.plus.app X).hom (Bass.minus.app X).hom
      (nativePlus.app X).hom (nativeMinus.app X).hom := by
  have hm : IsPullback (Bass.minus.app X).hom
      (pullback.snd (toIntegerBase X.obj) (PolynomialLaurent.laurentProjection integerRing))
      (pullback.snd (toIntegerBase X.obj) (PolynomialLaurent.polynomialProjection integerRing))
      (PolynomialLaurent.laurentMinus integerRing) :=
    baseProductTransformation_isPullback _ _ _
      (PolynomialLaurent.laurentMinus_projection integerRing) X.obj
  have hp : (Bass.plus.app X).hom ≫
      pullback.snd (toIntegerBase X.obj) (PolynomialLaurent.polynomialProjection integerRing) =
      pullback.snd (toIntegerBase X.obj) (PolynomialLaurent.laurentProjection integerRing) ≫
        PolynomialLaurent.laurentPlus integerRing := by
    simp [Bass.plus, qcBaseProductTransformation, baseProductTransformation]
  have hout : IsPullback (Bass.minus.app X).hom
      ((Bass.plus.app X).hom ≫ pullback.snd (toIntegerBase X.obj)
        (PolynomialLaurent.polynomialProjection integerRing))
      ((nativeMinus.app X).hom ≫ nativeIntegerProjection X) (plusChart integerRing) := by
    rw [hp, (nativeMinus_isPullback X).w]
    exact hm.paste_vert (chart_isPullback integerRing).flip
  exact (hout.of_bot (congrArg (fun f => f.hom) (native_overlap X)).symm
    (nativePlus_isPullback X)).flip

/-- The canonical affine-base projective-line comparison is cartesian. -/
theorem nativeAffine_isPullback (R : CommRingCat.{u}) :
    IsPullback (projection R) (coefficientMap (integerMap R))
      (toIntegerBase (Spec R)) (projection integerRing) := by
  simpa only [spec_integerMap] using (coefficientMap_isPullback (integerMap R)).flip

/-- Compare the installed affine line with the actual common-integer native product. -/
def nativeAffineIso (R : CommRingCat.{u}) :
    twoChartLine R ≅ (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj :=
  (nativeAffine_isPullback R).isoPullback

/-- This comparison retains the installed affine projection. -/
@[reassoc (attr := simp)]
theorem nativeAffineIso_projection (R : CommRingCat.{u}) :
    (nativeAffineIso R).hom ≫ (nativeProjection.app ⟨Spec R, inferInstance⟩).hom =
      projection R :=
  (nativeAffine_isPullback R).isoPullback_hom_fst

/-- This comparison retains the original integer coefficient map. -/
@[reassoc (attr := simp)]
theorem nativeAffineIso_integerProjection (R : CommRingCat.{u}) :
    (nativeAffineIso R).hom ≫ nativeIntegerProjection ⟨Spec R, inferInstance⟩ =
      coefficientMap (integerMap R) :=
  (nativeAffine_isPullback R).isoPullback_hom_snd

/-- The positive chart is preserved through the already installed polynomial comparison. -/
@[reassoc]
theorem nativeAffineIso_plus (R : CommRingCat.{u}) :
    plusChart R ≫ (nativeAffineIso R).hom =
      (polynomialSpecIso R).hom ≫ (nativePlus.app ⟨Spec R, inferInstance⟩).hom := by
  apply pullback.hom_ext
  · change _ ≫ (nativeProjection.app ⟨Spec R, inferInstance⟩).hom =
      _ ≫ (nativeProjection.app ⟨Spec R, inferInstance⟩).hom
    rw [Category.assoc, nativeAffineIso_projection, plusChart_projection, Category.assoc]
    rw [← ObjectProperty.FullSubcategory.comp_hom, nativePlus_projection]
    exact (polynomialSpecIso_hom_fst R).symm
  · change _ ≫ nativeIntegerProjection ⟨Spec R, inferInstance⟩ =
      _ ≫ nativeIntegerProjection ⟨Spec R, inferInstance⟩
    rw [Category.assoc, nativeAffineIso_integerProjection, plusChart_coefficientMap,
      Category.assoc, (nativePlus_isPullback _).w, ← Category.assoc,
      polynomialSpecIso_hom_snd]

/-- The inverse-coordinate chart is preserved through the same polynomial comparison. -/
@[reassoc]
theorem nativeAffineIso_minus (R : CommRingCat.{u}) :
    minusChart R ≫ (nativeAffineIso R).hom =
      (polynomialSpecIso R).hom ≫ (nativeMinus.app ⟨Spec R, inferInstance⟩).hom := by
  apply pullback.hom_ext
  · change _ ≫ (nativeProjection.app ⟨Spec R, inferInstance⟩).hom =
      _ ≫ (nativeProjection.app ⟨Spec R, inferInstance⟩).hom
    rw [Category.assoc, nativeAffineIso_projection, minusChart_projection, Category.assoc]
    rw [← ObjectProperty.FullSubcategory.comp_hom, nativeMinus_projection]
    exact (polynomialSpecIso_hom_fst R).symm
  · change _ ≫ nativeIntegerProjection ⟨Spec R, inferInstance⟩ =
      _ ≫ nativeIntegerProjection ⟨Spec R, inferInstance⟩
    rw [Category.assoc, nativeAffineIso_integerProjection, minusChart_coefficientMap,
      Category.assoc, (nativeMinus_isPullback _).w, ← Category.assoc,
      polynomialSpecIso_hom_snd]

end AlgebraicGeometry.Scheme.ProjectiveLine
