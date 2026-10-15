/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeCoefficientTensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOne

/-! # The literal native shifted coefficient and exact coefficient pair

The actual coefficient is right tensor, original Godement total, ordinary
native projection and the signed cochain shift by one. Its derived comparison
retains the installed unit, original total augmentation and shift comparisons.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients
open FlasqueCoefficients

/-- The standard derived-category instance for sheaves of modules on `Y`. -/
local instance nativeCoefficientStandardDerived (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

/-- The original prescribed K tensor L with its existing strict lower bound. -/
def rightTensorPlus (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ CochainComplex.Plus
      (nativeLineFunctor.obj X).obj.Modules :=
  rightTensor X ⋙ boundedToPlus (nativeLineFunctor.obj X).obj

/-- Actual Godement totalization after the original right tensor. -/
def rightTensorTotal (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ FlasqueBoundedBelow.Obj
      (nativeLineFunctor.obj X).obj :=
  rightTensor X ⋙ FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj

lemma rightTensorTotal_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (rightTensorTotal X) :=
  (rightTensor_exact X).comp (FlasqueBoundedBelow.total_exact (nativeLineFunctor.obj X).obj)

/-- The requested actual original one coefficient p_*T(K tensor L)[1]. -/
def G1 (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ FlasqueBoundedBelow.Obj X.obj :=
  rightTensorTotal X ⋙ G0 X ⋙ modelShift X.obj 1

/-- The exact original coefficient preserves zero, cofibrations, weak maps and pushouts. -/
lemma G1_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (G1 X) :=
  (rightTensorTotal_exact X).comp ((G0_exact X).comp (modelShift_exact X.obj 1))

/-- The underlying coefficient is the exact requested original cochain object. -/
lemma G1_obj_underlying (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    ((G1 X).obj K).obj =
      ((((Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex (.up
        ℤ)).obj
        ((godementTotal (nativeLineFunctor.obj X).obj).obj
          ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (nativeTautologicalLine X)).obj
            K.obj)))⟦(1 : ℤ)⟧) := rfl

/-- The underlying arrows retain the original tensor, total, direct image and shift maps. -/
lemma G1_map_underlying (X : QuasiCompactSchemes.{u})
    {K L : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj} (f : K ⟶ L) :
    ((G1 X).map f).hom =
      ((((Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex (.up
        ℤ)).map
        ((godementTotal (nativeLineFunctor.obj X).obj).map
          ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (nativeTautologicalLine X)).map
            f.hom)))⟦(1 : ℤ)⟧') := rfl

/-- A specified original bound a becomes exactly a-1 after the actual shift by one. -/
lemma G1_isStrictlyGE (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((G1 X).obj K).obj.IsStrictlyGE (a - 1) := by
  have ht : ((rightTensor X).obj K).obj.IsStrictlyGE a :=
    rightTensor_isStrictlyGE X K.obj a
  let := ht
  have hT : ((rightTensorTotal X).obj K).obj.IsStrictlyGE a :=
    FlasqueBoundedBelow.total_isStrictlyGE _ _ a
  let := hT
  have hp : ((G0 X).obj ((rightTensorTotal X).obj K)).obj.IsStrictlyGE a :=
    G0Raw_isStrictlyGE X _ a
  let := hp
  change ((((G0 X).obj ((rightTensorTotal X).obj K)).obj)⟦(1 : ℤ)⟧).IsStrictlyGE (a - 1)
  exact CochainComplex.isStrictlyGE_shift
    ((G0 X).obj ((rightTensorTotal X).obj K)).obj a 1 (a - 1) (by omega)

/-- The original actual total augmentation in the precise full-model source. -/
def tensorTotalUnit (X : QuasiCompactSchemes.{u}) :
    rightTensorPlus X ⟶ rightTensorTotal X ⋙ toPlus (nativeLineFunctor.obj X).obj where
  app K := ObjectProperty.homMk
    ((godementTotalUnit (nativeLineFunctor.obj X).obj).app ((rightTensorPlus X).obj K).obj)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (godementTotalUnit (nativeLineFunctor.obj X).obj).naturality ((rightTensorPlus X).map
      f).hom

instance tensorTotalUnit_quasiIso (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    QuasiIso ((tensorTotalUnit X).app K).hom :=
  godementTotalUnit_quasiIso (nativeLineFunctor.obj X).obj ((rightTensorPlus X).obj K)

/-- The actual augmentation transported by the installed derived projection. -/
def tensorTotalDerivedAugmentation (X : QuasiCompactSchemes.{u}) :
    rightTensorPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (nativeProjection.app
      X).hom ⟶
      rightTensorTotal X ⋙ toPlus (nativeLineFunctor.obj X).obj ⋙ DerivedCategory.Plus.Q ⋙
        derivedPushforwardPlus (nativeProjection.app X).hom :=
  CategoryTheory.Functor.whiskerRight (tensorTotalUnit X)
    (DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (nativeProjection.app X).hom)

instance tensorTotalDerivedAugmentation_isIso (X : QuasiCompactSchemes.{u}) :
    IsIso (tensorTotalDerivedAugmentation X) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  have : IsIso (DerivedCategory.Plus.Q.map ((tensorTotalUnit X).app K)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (nativeLineFunctor.obj X).obj.Modules) _
      (tensorTotalUnit_quasiIso X K)
  exact inferInstanceAs (IsIso ((derivedPushforwardPlus (nativeProjection.app X).hom).map
    (DerivedCategory.Plus.Q.map ((tensorTotalUnit X).app K))))

/-- Natural comparison retains the actual installed unit and actual original augmentation. -/
def unshiftedDerivedIso (X : QuasiCompactSchemes.{u}) :
    rightTensorTotal X ⋙ G0 X ⋙ toPlus X.obj ⋙ DerivedCategory.Plus.Q ≅
      rightTensorPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (nativeProjection.app
        X).hom :=
  Functor.isoWhiskerLeft (rightTensorTotal X) (G0DerivedIso X) ≪≫
    (asIso (tensorTotalDerivedAugmentation X)).symm

/-- Composing with the actual original derived augmentation recovers the installed unit. -/
lemma unshiftedDerivedIso_unit_correspondence (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    (unshiftedDerivedIso X).hom.app K ≫ (tensorTotalDerivedAugmentation X).app K =
      (G0DerivedIso X).hom.app ((rightTensorTotal X).obj K) := by
  change ((G0DerivedIso X).hom.app ((rightTensorTotal X).obj K) ≫
      (asIso (tensorTotalDerivedAugmentation X)).inv.app K) ≫
      (asIso (tensorTotalDerivedAugmentation X)).hom.app K = _
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The transported original augmentation is the admitted total-derived augmentation. -/
lemma tensorTotalDerivedAugmentation_app (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    (tensorTotalDerivedAugmentation X).app K =
      (godementTotalDerivedAugmentation (nativeProjection.app X).hom).app ((rightTensorPlus
        X).obj K) := rfl

/-- The comparison recovers precisely the actual installed direct-image unit. -/
lemma unshiftedDerivedIso_installed_unit (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    (unshiftedDerivedIso X).hom.app K ≫ (tensorTotalDerivedAugmentation X).app K =
      (derivedPushforwardPlusUnit (nativeProjection.app X).hom).app
        ((toPlus (nativeLineFunctor.obj X).obj).obj ((rightTensorTotal X).obj K)) :=
  (unshiftedDerivedIso_unit_correspondence X K).trans
    (G0DerivedIso_hom_app X ((rightTensorTotal X).obj K))

/-- The natural installed-derived comparison for the exact original G1 functor. -/
def G1DerivedIso (X : QuasiCompactSchemes.{u}) :
    G1 X ⋙ toPlus X.obj ⋙ DerivedCategory.Plus.Q ≅
      rightTensorPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (nativeProjection.app
        X).hom ⋙
        shiftFunctor (DerivedCategory.Plus X.obj.Modules) (1 : ℤ) :=
  Functor.isoWhiskerLeft (rightTensorTotal X ⋙ G0 X) (modelShiftDerivedIso X.obj 1) ≪≫
    Functor.isoWhiskerRight (unshiftedDerivedIso X)
      (shiftFunctor (DerivedCategory.Plus X.obj.Modules) (1 : ℤ))

/-- The original component retains both native shift comparisons and the original unit. -/
lemma G1DerivedIso_hom_app (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    (G1DerivedIso X).hom.app K =
      DerivedCategory.Plus.Q.map ((modelShiftPlusIso X.obj 1).hom.app
          ((G0 X).obj ((rightTensorTotal X).obj K))) ≫
        (DerivedCategory.Plus.Q.commShiftIso (1 : ℤ)).hom.app
          ((toPlus X.obj).obj ((G0 X).obj ((rightTensorTotal X).obj K))) ≫
        (shiftFunctor (DerivedCategory.Plus X.obj.Modules) (1 : ℤ)).map
          ((unshiftedDerivedIso X).hom.app K) := by
  change (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
  exact Category.assoc _ _ _

/-- The shifted original augmentation recovers the shifted installed derived unit. -/
lemma G1DerivedIso_unit_correspondence (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    (G1DerivedIso X).hom.app K ≫
        (shiftFunctor (DerivedCategory.Plus X.obj.Modules) (1 : ℤ)).map
          ((tensorTotalDerivedAugmentation X).app K) =
      DerivedCategory.Plus.Q.map ((modelShiftPlusIso X.obj 1).hom.app
          ((G0 X).obj ((rightTensorTotal X).obj K))) ≫
        (DerivedCategory.Plus.Q.commShiftIso (1 : ℤ)).hom.app
          ((toPlus X.obj).obj ((G0 X).obj ((rightTensorTotal X).obj K))) ≫
        (shiftFunctor (DerivedCategory.Plus X.obj.Modules) (1 : ℤ)).map
          ((G0DerivedIso X).hom.app ((rightTensorTotal X).obj K)) := by
  rw [G1DerivedIso_hom_app, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, unshiftedDerivedIso_unit_correspondence]

/-- Naturality compares the actual original coefficient maps with the prescribed derived maps. -/
@[reassoc]
lemma G1DerivedIso_naturality (X : QuasiCompactSchemes.{u})
    {K L : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj} (f : K ⟶ L) :
    DerivedCategory.Plus.Q.map ((toPlus X.obj).map ((G1 X).map f)) ≫
        (G1DerivedIso X).hom.app L =
      (G1DerivedIso X).hom.app K ≫
        (shiftFunctor (DerivedCategory.Plus X.obj.Modules) (1 : ℤ)).map
          ((derivedPushforwardPlus (nativeProjection.app X).hom).map
            (DerivedCategory.Plus.Q.map ((rightTensorPlus X).map f))) :=
  (G1DerivedIso X).hom.naturality f

/-- Actual product coefficient functor with both original exact coefficient maps. -/
def G (X : QuasiCompactSchemes.{u}) : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤
    FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj :=
  (G0 X).prod' (G1 X)

/-- The product coefficient functor is exact for the actual product Waldhausen structure. -/
lemma G_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).weq
    (G X) :=
  Waldhausen.ExtensionCategory.pair_exact _ _ _ (G0_exact X) (G1_exact X)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients
