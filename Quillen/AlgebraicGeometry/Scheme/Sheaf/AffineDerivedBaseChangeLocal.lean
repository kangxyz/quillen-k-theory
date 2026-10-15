/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedBaseChangeCoordinates
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeBaseOpen
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeOpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine-morphism derived base change on quasicoherent single sheaves -/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived category of module sheaves. -/
local instance affineTargetCoverStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
/-- Actual affine-chart localization discharges the target for the original flat mate. -/
theorem isIso_derivedFlatBaseChangeMap_affineSource_single
    {W U V X : Scheme.{u}} [IsAffine U] [IsAffine X]
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j] (M : U.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
  let Y := V.affineCover.X
  let k := V.affineCover.f
  let Z := fun i => pullback b (k i)
  let c := fun i => pullback.fst b (k i)
  let d := fun i => pullback.snd b (k i)
  have hs (i) : IsPullback (c i) (d i) b (k i) := IsPullback.of_hasPullback b (k i)
  apply isIso_derivedFlatBaseChangeMap_of_openCover a b f j h Y Z k c d hs
    (fun x => V.affineCover.exists_eq x)
  intro i
  have : IsAffine (Z i) := IsAffine.of_isPullback ((hs i).paste_horiz h).flip
  exact isIso_derivedFlatBaseChangeMap_affine_single (c i ≫ a) (d i) f (k i ≫ j)
    ((hs i).paste_horiz h) M
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived category of module sheaves. -/
local instance affineMorphismBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
/-- Affine direct-image flat base change for actual quasicoherent single sheaves. -/
theorem isIso_derivedFlatBaseChangeMap_affineHom_single
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [IsAffineHom f] [Flat j]
    (M : U.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
  let C := X.affineCover
  let D := C.pullback₁ j
  let Y := D.X
  let k := D.f
  let Z := fun i => pullback b (k i)
  let c := fun i => pullback.fst b (k i)
  let d := fun i => pullback.snd b (k i)
  have hs (i) : IsPullback (c i) (d i) b (k i) := IsPullback.of_hasPullback b (k i)
  apply isIso_derivedFlatBaseChangeMap_of_openCover a b f j h Y Z k c d hs
    (fun x => Scheme.Cover.exists_eq D x)
  intro i
  let e := C.f i
  let l := pullback.snd j e
  let A := pullback f e
  let aa := pullback.fst f e
  let ff := pullback.snd f e
  have he : IsPullback aa ff f e := IsPullback.of_hasPullback f e
  have hj : IsPullback (k i) l j e := IsPullback.of_hasPullback j e
  let := flat_cartesian_baseChange l (k i) e j hj.flip
  have big : IsPullback (c i ≫ a) (d i) f (l ≫ e) := by
    rw [← hj.w]
    exact (hs i).paste_horiz h
  let cc := he.lift (c i ≫ a) (d i ≫ l) (by rw [big.w, Category.assoc])
  have small : IsPullback cc (d i) ff l := big.of_right' he
  have : IsAffine A := inferInstance
  have : ((Scheme.Modules.pullback aa).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent A.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback aa).app M) (by infer_instance)
  have localIso := isIso_derivedFlatBaseChangeMap_affineSource_single cc (d i) ff l small
    ((Scheme.Modules.pullback aa).obj M)
  have largeIso := (isIso_derivedFlatBaseChangeMap_baseOpen_single_iff cc (d i) l
    aa ff f e small he M).mp localIso
  apply (derivedFlatBaseChangeMap_congr_iff (he.lift_fst _ _ _) rfl rfl hj.w.symm
    (small.paste_horiz he) ((hs i).paste_horiz h)
    ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)).mp
  exact largeIso
end AlgebraicGeometry.Scheme.Modules
