/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.QuasiCoherent
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Affine

/-! # Affine quasicoherent single-sheaf derived base change -/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Use the original standard derived categories of actual module sheaves. -/
local instance affineDerivedBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

variable (h : IsPullback
  (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (Spec.map (CommRingCat.ofHom (algebraMap S B)))
  (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- The original ordinary affine mate is invertible on the actual single QC complex. -/

theorem isIso_affineBaseChangeMap_singleComplex
    (M : (Spec (CommRingCat.of A)).Modules) [M.IsQuasicoherent] :
    IsIso ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap _ _ _ _ h)).app
      (singleZeroPlus (Spec (CommRingCat.of A)) M)) := by
  apply NatTrans.isIso_mapCochainComplexPlus_app
  intro n
  by_cases hn : n = 0
  · subst n
    change IsIso ((cartesianBaseChangeMap _ _ _ _ h).app
      (((HomologicalComplex.single (Spec (CommRingCat.of A)).Modules (.up ℤ) 0).obj M).X 0))
    rw [HomologicalComplex.single_obj_X_self]
    exact isIso_affineBaseChangeMap R S A B h M
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn
    exact (Functor.map_isZero _ hz).isIso (Functor.map_isZero _ hz) _

/-- The original derived flat base-change map is invertible on an actual single affine
quasicoherent sheaf. -/

theorem isIso_derivedFlatBaseChangeMap_single
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (M : (Spec (CommRingCat.of A)).Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap _ _ _ _ h).app
      (DerivedCategory.Plus.Q.obj (singleZeroPlus (Spec (CommRingCat.of A)) M))) := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let b := Spec.map (CommRingCat.ofHom (algebraMap S B))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let j := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let := flat_cartesian_baseChange a b f j h
  let F := Scheme.Modules.pushforward f
  let J := Scheme.Modules.pullback j
  let P := Scheme.Modules.pullback a
  let G := Scheme.Modules.pushforward b
  let K := singleZeroPlus (Spec (CommRingCat.of A)) M
  have : IsIso J.rightDerivedFunctorPlusUnit := isIso_derivedFlatPullbackPlusUnit j
  have : IsIso P.rightDerivedFunctorPlusUnit := isIso_derivedFlatPullbackPlusUnit a
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K) :=
    isIso_derivedPushforwardPlusUnit_single f M
  have : (P.obj M).IsQuasicoherent :=
    isQuasicoherent_pullback (CommRingCat.ofHom (algebraMap A B)) M
  have : IsIso (G.rightDerivedFunctorPlusUnit.app
      (singleZeroPlus (Spec (CommRingCat.of B)) (P.obj M))) :=
    isIso_derivedPushforwardPlusUnit_single b (P.obj M)
  let e : P.mapCochainComplexPlus.obj K ≅
      singleZeroPlus (Spec (CommRingCat.of B)) (P.obj M) :=
    (CochainComplex.plus (Spec (CommRingCat.of B)).Modules).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app M)
  have : IsIso (G.rightDerivedFunctorPlusUnit.app (P.mapCochainComplexPlus.obj K)) :=
    (NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorPlusUnit e).mpr inferInstance
  have hleft : IsIso ((Functor.rightDerivedFunctorPlusCompUnit F J).app K) := by
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    infer_instance
  have hright : IsIso ((Functor.rightDerivedFunctorPlusCompUnit P G).app K) := by
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    infer_instance
  have : IsIso ((NatTrans.mapCochainComplexPlus
      (cartesianBaseChangeMap a b f j h)).app K) :=
    isIso_affineBaseChangeMap_singleComplex R S A B h M
  have hc : IsIso ((Functor.rightDerivedFunctorPlusCompUnit F J).app K ≫
      (derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)) := by
    rw [derivedFlatBaseChangeMap_unit]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hc

end AlgebraicGeometry.Scheme.Modules
