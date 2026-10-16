/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.ShiftPlus


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Plus


public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOperations
public import Quillen.Waldhausen.ExtensionCategory.Product

/-!
# The exact original shifted tautological coefficient

G1 is literal right tensor by the actual negative line, actual Godement total,
ordinary projection, and original shift by one. Its natural comparison retains
the original installed derived unit, the actual total augmentation, and the
native localization shift isomorphism. No K-map inverse or additivity is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules.Godement
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

attribute [local instance] coefficientStandardDerived

/-- The original prescribed K tensor L with its existing strict lower bound. -/
def rightTensorPlus (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  rightTensor R ⋙ boundedToPlus (twoChartLine R)

/-- Actual Godement totalization after the original right tensor. -/
def rightTensorTotal (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  rightTensor R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma rightTensorTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (rightTensorTotal R) :=
  (rightTensor_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- The requested actual original one coefficient p_*T(K tensor L)[1]. -/
def G1 (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (Spec R) :=
  rightTensorTotal R ⋙ G0 R ⋙ modelShift (Spec R) 1

/-- The exact original coefficient preserves zero, cofibrations, weak maps and pushouts. -/
lemma G1_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (G1 R) :=
  (rightTensorTotal_exact R).comp ((G0_exact R).comp (modelShift_exact (Spec R) 1))

/-- The underlying coefficient is the exact requested original cochain object. -/
lemma G1_obj_underlying (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((G1 R).obj K).obj =
      ((((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).obj
        ((godementTotal (twoChartLine R)).obj
          ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).obj
            K.obj)))⟦(1 : ℤ)⟧) := rfl

/-- The underlying arrows retain the original tensor, total, direct image and shift maps. -/
lemma G1_map_underlying (R : CommRingCat.{u})
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((G1 R).map f).hom =
      ((((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (twoChartLine R)).map
          ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).map
            f.hom)))⟦(1 : ℤ)⟧') := rfl

/-- A specified original bound a becomes exactly a-1 after the actual shift by one. -/
lemma G1_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((G1 R).obj K).obj.IsStrictlyGE (a - 1) := by
  have ht : ((rightTensor R).obj K).obj.IsStrictlyGE a :=
    rightTensor_isStrictlyGE R K.obj a
  let := ht
  have hT : ((rightTensorTotal R).obj K).obj.IsStrictlyGE a :=
    FlasqueBoundedBelow.total_isStrictlyGE _ _ a
  let := hT
  have hp : ((G0 R).obj ((rightTensorTotal R).obj K)).obj.IsStrictlyGE a :=
    G0Raw_isStrictlyGE R _ a
  let := hp
  change ((((G0 R).obj ((rightTensorTotal R).obj K)).obj)⟦(1 : ℤ)⟧).IsStrictlyGE (a - 1)
  exact CochainComplex.isStrictlyGE_shift
    ((G0 R).obj ((rightTensorTotal R).obj K)).obj a 1 (a - 1) (by omega)

/-- The original actual total augmentation in the precise full-model source. -/
def tensorTotalUnit (R : CommRingCat.{u}) :
    rightTensorPlus R ⟶ rightTensorTotal R ⋙ toPlus (twoChartLine R) where
  app K := ObjectProperty.homMk
    ((godementTotalUnit (twoChartLine R)).app ((rightTensorPlus R).obj K).obj)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (godementTotalUnit (twoChartLine R)).naturality ((rightTensorPlus R).map f).hom

instance tensorTotalUnit_quasiIso (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((tensorTotalUnit R).app K).hom :=
  godementTotalUnit_quasiIso (twoChartLine R) ((rightTensorPlus R).obj K)

/-- The actual augmentation transported by the installed derived projection. -/
def tensorTotalDerivedAugmentation (R : CommRingCat.{u}) :
    rightTensorPlus R ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R) ⟶
      rightTensorTotal R ⋙ toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ⋙
        derivedPushforwardPlus (projection R) :=
  CategoryTheory.Functor.whiskerRight (tensorTotalUnit R)
    (DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R))

instance tensorTotalDerivedAugmentation_isIso (R : CommRingCat.{u}) :
    IsIso (tensorTotalDerivedAugmentation R) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  have : IsIso (DerivedCategory.Plus.Q.map ((tensorTotalUnit R).app K)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (twoChartLine R).Modules) _
      (tensorTotalUnit_quasiIso R K)
  exact inferInstanceAs (IsIso ((derivedPushforwardPlus (projection R)).map
    (DerivedCategory.Plus.Q.map ((tensorTotalUnit R).app K))))

/-- Natural comparison retains the actual installed unit and actual original augmentation. -/
def unshiftedDerivedIso (R : CommRingCat.{u}) :
    rightTensorTotal R ⋙ G0 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ≅
      rightTensorPlus R ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R) :=
  Functor.isoWhiskerLeft (rightTensorTotal R) (G0DerivedIso R) ≪≫
    (asIso (tensorTotalDerivedAugmentation R)).symm

/-- Composing with the actual original derived augmentation recovers the installed unit. -/
lemma unshiftedDerivedIso_unit_correspondence (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (unshiftedDerivedIso R).hom.app K ≫ (tensorTotalDerivedAugmentation R).app K =
      (G0DerivedIso R).hom.app ((rightTensorTotal R).obj K) := by
  change ((G0DerivedIso R).hom.app ((rightTensorTotal R).obj K) ≫
      (asIso (tensorTotalDerivedAugmentation R)).inv.app K) ≫
      (asIso (tensorTotalDerivedAugmentation R)).hom.app K = _
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The transported original augmentation is the admitted total-derived augmentation. -/
lemma tensorTotalDerivedAugmentation_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (tensorTotalDerivedAugmentation R).app K =
      (godementTotalDerivedAugmentation (projection R)).app ((rightTensorPlus R).obj K) := rfl

/-- The comparison recovers precisely the actual installed direct-image unit. -/
lemma unshiftedDerivedIso_installed_unit (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (unshiftedDerivedIso R).hom.app K ≫ (tensorTotalDerivedAugmentation R).app K =
      (derivedPushforwardPlusUnit (projection R)).app
        ((toPlus (twoChartLine R)).obj ((rightTensorTotal R).obj K)) :=
  (unshiftedDerivedIso_unit_correspondence R K).trans
    (G0DerivedIso_hom_app R ((rightTensorTotal R).obj K))

/-- The natural installed-derived comparison for the exact original G1 functor. -/
def G1DerivedIso (R : CommRingCat.{u}) :
    G1 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ≅
      rightTensorPlus R ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R) ⋙
        shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ) :=
  Functor.isoWhiskerLeft (rightTensorTotal R ⋙ G0 R) (modelShiftDerivedIso (Spec R) 1) ≪≫
    Functor.isoWhiskerRight (unshiftedDerivedIso R)
      (shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ))

/-- The original component retains both native shift comparisons and the original unit. -/
lemma G1DerivedIso_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (G1DerivedIso R).hom.app K =
      DerivedCategory.Plus.Q.map ((modelShiftPlusIso (Spec R) 1).hom.app
          ((G0 R).obj ((rightTensorTotal R).obj K))) ≫
        (DerivedCategory.Plus.Q.commShiftIso (1 : ℤ)).hom.app
          ((toPlus (Spec R)).obj ((G0 R).obj ((rightTensorTotal R).obj K))) ≫
        (shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ)).map
          ((unshiftedDerivedIso R).hom.app K) := by
  change (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
  exact Category.assoc _ _ _

/-- The shifted original augmentation recovers the shifted installed derived unit. -/
lemma G1DerivedIso_unit_correspondence (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (G1DerivedIso R).hom.app K ≫
        (shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ)).map
          ((tensorTotalDerivedAugmentation R).app K) =
      DerivedCategory.Plus.Q.map ((modelShiftPlusIso (Spec R) 1).hom.app
          ((G0 R).obj ((rightTensorTotal R).obj K))) ≫
        (DerivedCategory.Plus.Q.commShiftIso (1 : ℤ)).hom.app
          ((toPlus (Spec R)).obj ((G0 R).obj ((rightTensorTotal R).obj K))) ≫
        (shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ)).map
          ((G0DerivedIso R).hom.app ((rightTensorTotal R).obj K)) := by
  rw [G1DerivedIso_hom_app, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, unshiftedDerivedIso_unit_correspondence]

/-- Naturality compares the actual original coefficient maps with the prescribed derived maps. -/
@[reassoc]
lemma G1DerivedIso_naturality (R : CommRingCat.{u})
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    DerivedCategory.Plus.Q.map ((toPlus (Spec R)).map ((G1 R).map f)) ≫
        (G1DerivedIso R).hom.app L =
      (G1DerivedIso R).hom.app K ≫
        (shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ)).map
          ((derivedPushforwardPlus (projection R)).map
            (DerivedCategory.Plus.Q.map ((rightTensorPlus R).map f))) :=
  (G1DerivedIso R).hom.naturality f

/-- Actual product coefficient functor with both original exact coefficient maps. -/
def G (R : CommRingCat.{u}) : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    FlasqueBoundedBelow.Obj (Spec R) × FlasqueBoundedBelow.Obj (Spec R) :=
  (G0 R).prod' (G1 R)

/-- The product coefficient functor is exact for the actual product Waldhausen structure. -/
lemma G_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).weq
    (G R) :=
  Waldhausen.ExtensionCategory.pair_exact _ _ _ (G0_exact R) (G1_exact R)

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
