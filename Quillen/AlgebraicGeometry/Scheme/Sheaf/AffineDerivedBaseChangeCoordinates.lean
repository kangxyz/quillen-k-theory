/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeCoordinates
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedBaseChange
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Derived base change on actual affine cartesian squares -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
/-- The standard derived category of module sheaves. -/
local instance specCoordinateStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
/-- The actual affine coordinate map is the spectrum of the original map on global sections. -/
theorem isoSpec_coordinate {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom = Spec.map f.appTop := by
  rw [← Scheme.isoSpec_inv_naturality_assoc]
  simp
variable {W U V X : Scheme.{u}} [IsAffine W] [IsAffine U] [IsAffine V] [IsAffine X]
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j)
include h
/-- The original cartesian square in its actual affine coordinate rings. -/
theorem specCoordinatePullback :
    IsPullback (Spec.map a.appTop) (Spec.map b.appTop)
      (Spec.map f.appTop) (Spec.map j.appTop) := by
  have hc := coordinatePullback a b f j h W.isoSpec.symm U.isoSpec.symm
    V.isoSpec.symm X.isoSpec
  simpa only [Iso.symm_hom, Iso.symm_inv, isoSpec_coordinate] using hc
/-- Affine coordinates retain the original derived mate on the actual pulled-back sheaf. -/
theorem isIso_derivedFlatBaseChangeMap_specCoordinates_iff [Flat j] (M : U.Modules) :
    letI : Flat (Spec.map j.appTop) := by
      rw [← isoSpec_coordinate j]
      infer_instance
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ↔
    IsIso ((derivedFlatBaseChangeMap _ _ _ _ (specCoordinatePullback a b f j h)).app
      ((DerivedCategory.Plus.singleFunctor (Spec Γ(U, ⊤)).Modules 0).obj
        ((Scheme.Modules.pullback U.isoSpec.inv).obj M))) := by
  let : Flat (Spec.map j.appTop) := by
    rw [← isoSpec_coordinate j]
    infer_instance
  apply (isIso_derivedFlatBaseChangeMap_coordinates_iff a b f j h
    W.isoSpec.symm U.isoSpec.symm V.isoSpec.symm X.isoSpec M).trans
  exact derivedFlatBaseChangeMap_congr_iff (isoSpec_coordinate a) (isoSpec_coordinate b)
    (isoSpec_coordinate f) (isoSpec_coordinate j) _ _ _
omit [IsAffine W] [IsAffine V] [IsAffine X] h in
/-- The actual affine-coordinate pullback of a quasicoherent sheaf is quasicoherent. -/
theorem isQuasicoherent_isoSpec_pullback (M : U.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback U.isoSpec.inv).obj M).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent (Spec Γ(U, ⊤)).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.isoSpec.inv).app M) (by infer_instance)
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- The standard derived category of module sheaves. -/
local instance affineGeneralStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable {R S A B : CommRingCat.{u}}
  (a : A ⟶ B) (b : S ⟶ B) (f : R ⟶ A) (j : R ⟶ S)
  (h : IsPullback (Spec.map a) (Spec.map b) (Spec.map f) (Spec.map j))
/-- The same affine single-sheaf theorem for arbitrary original ring homomorphisms. -/
theorem isIso_derivedFlatBaseChangeMap_spec_single [Flat (Spec.map j)]
    (M : (Spec A).Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap _ _ _ _ h).app
      ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj M)) := by
  let : Algebra R S := j.hom.toAlgebra
  let : Algebra R A := f.hom.toAlgebra
  let : Algebra A B := a.hom.toAlgebra
  let : Algebra S B := b.hom.toAlgebra
  let : Algebra R B := (a.hom.comp f.hom).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have hc : f ≫ a = j ≫ b := by
    apply Spec.map_injective
    simpa only [Spec.map_comp] using h.w
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom hc)
  exact isIso_derivedFlatBaseChangeMap_single R S A B h M
/-- The original derived flat base-change map on an arbitrary affine cartesian square
is invertible on each actual quasicoherent single sheaf. -/
theorem isIso_derivedFlatBaseChangeMap_affine_single
    {W U V X : Scheme.{u}} [IsAffine W] [IsAffine U] [IsAffine V] [IsAffine X]
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j] (M : U.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
  let : Flat (Spec.map j.appTop) := by
    rw [← isoSpec_coordinate j]
    infer_instance
  have := isQuasicoherent_isoSpec_pullback M
  apply (isIso_derivedFlatBaseChangeMap_specCoordinates_iff a b f j h M).mpr
  exact isIso_derivedFlatBaseChangeMap_spec_single a.appTop b.appTop f.appTop j.appTop
    (specCoordinatePullback a b f j h) ((Scheme.Modules.pullback U.isoSpec.inv).obj M)
end Quillen.SchemeSheaf
