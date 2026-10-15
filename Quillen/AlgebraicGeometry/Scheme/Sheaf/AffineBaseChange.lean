/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineScalarSquare

/-! # Ordinary affine quasicoherent base change with the original mate

Under the original tilde pullback and pushforward comparisons, the geometric mate is
exactly the scalar base-change mate. Consequently it is invertible for every
quasicoherent sheaf on a genuine cartesian square of affine spectra. Neither flatness
nor finite generation is required. This is an ordinary sheaf statement; it does not
assert derived flat base change.
-/
@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]
variable (h : IsPullback
  (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (Spec.map (CommRingCat.ofHom (algebraMap S B)))
  (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (Spec.map (CommRingCat.ofHom (algebraMap R S))))
/-- The source comparison for the actual affine base-change mate. -/
def affineBaseChangeSourceIso (M : ModuleCat A) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj
          (tilde M)) ≅
      tilde ((ModuleCat.extendScalars (algebraMap R S)).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj M)) :=
  (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapIso
    ((tildePushforwardIso (CommRingCat.ofHom (algebraMap R A))).app M) ≪≫
    (tildePullbackIso (CommRingCat.ofHom (algebraMap R S))).app
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M)
/-- The target comparison for the actual affine base-change mate. -/
def affineBaseChangeTargetIso (M : ModuleCat A) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap S B)))).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
          (tilde M)) ≅
      tilde ((ModuleCat.restrictScalars (algebraMap S B)).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M)) :=
  (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap S B)))).mapIso
    ((tildePullbackIso (CommRingCat.ofHom (algebraMap A B))).app M) ≪≫
    (tildePushforwardIso (CommRingCat.ofHom (algebraMap S B))).app
      ((ModuleCat.extendScalars (algebraMap A B)).obj M)
/-- The original affine geometric base-change mate is the actual scalar base-change mate. -/
theorem affineBaseChangeMap_tilde (M : ModuleCat A) :
    (cartesianBaseChangeMap _ _ _ _ h).app (tilde M) ≫
      (affineBaseChangeTargetIso S A B M).hom =
    (affineBaseChangeSourceIso R S A M).hom ≫
      (tilde.functor (CommRingCat.of S)).map ((ModuleCat.scalarBaseChangeMap R S A B).app M) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply (cancel_mono ((tildePushforwardIso (CommRingCat.ofHom (algebraMap R S))).hom.app
    ((ModuleCat.restrictScalars (algebraMap S B)).obj
      ((ModuleCat.extendScalars (algebraMap A B)).obj M)))).mp
  simp only [affineBaseChangeSourceIso, affineBaseChangeTargetIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hm := cartesianBaseChangeMap_unit _ _ _ _ h (tilde M)
  erw [← reassoc_of% hm]
  have hj := (Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).unit.naturality
    ((tildePushforwardIso (CommRingCat.ofHom (algebraMap R A))).hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hj
  erw [← reassoc_of% hj]
  have hb := (tildePushforwardIso (CommRingCat.ofHom (algebraMap R S))).hom.naturality
    ((ModuleCat.scalarBaseChangeMap R S A B).app M)
  dsimp only [Functor.comp_map] at hb
  erw [hb]
  erw [reassoc_of% tildePullbackIso_unit (CommRingCat.ofHom (algebraMap R S))
    ((ModuleCat.restrictScalars (algebraMap R A)).obj M)]
  have hs := (cartesianPushforwardSquare _ _ _ _ h).hom.naturality
    ((tildePullbackIso (CommRingCat.ofHom (algebraMap A B))).hom.app M)
  dsimp only [Functor.comp_map] at hs
  erw [← reassoc_of% hs]
  erw [← tildePushforwardIso_square R S A B h ((ModuleCat.extendScalars (algebraMap A B)).obj M)]
  erw [← (Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map_comp_assoc]
  erw [← (Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map_comp_assoc]
  simp only [Category.assoc]
  erw [tildePullbackIso_unit (CommRingCat.ofHom (algebraMap A B)) M]
  have hf := (tildePushforwardIso (CommRingCat.ofHom (algebraMap R A))).hom.naturality
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).unit.app M)
  dsimp only [Functor.comp_map] at hf
  erw [reassoc_of% hf]
  rw [← (tilde.functor (CommRingCat.of R)).map_comp,
    ← (tilde.functor (CommRingCat.of R)).map_comp]
  exact congrArg (fun q =>
    (tildePushforwardIso (CommRingCat.ofHom (algebraMap R A))).hom.app M ≫
      (tilde.functor (CommRingCat.of R)).map q) (ModuleCat.scalarBaseChangeMap_unit R S A B M)
/-- The original affine geometric mate is invertible on associated sheaves over a ring pushout. -/
theorem isIso_affineBaseChangeMap_tilde (M : ModuleCat A) :
    IsIso ((cartesianBaseChangeMap _ _ _ _ h).app (tilde M)) := by
  have := isPushout_of_affineCartesian R S A B h
  have := ModuleCat.scalarBaseChangeMap_isIso R S A B
  have hc : IsIso ((cartesianBaseChangeMap _ _ _ _ h).app (tilde M) ≫
      (affineBaseChangeTargetIso S A B M).hom) := by
    rw [affineBaseChangeMap_tilde]
    infer_instance
  exact (isIso_comp_right_iff _ (affineBaseChangeTargetIso S A B M).hom).mp hc
/-- The actual affine base-change mate is invertible on every quasicoherent sheaf. -/
theorem isIso_affineBaseChangeMap
    (M : (Spec (CommRingCat.of A)).Modules) [M.IsQuasicoherent] :
    IsIso ((cartesianBaseChangeMap _ _ _ _ h).app M) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ (asIso M.fromTildeΓ)]
  exact isIso_affineBaseChangeMap_tilde R S A B h (moduleSpecΓFunctor.obj M)
end AlgebraicGeometry.Scheme.Modules
