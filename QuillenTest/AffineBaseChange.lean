/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.QuasiCoherent
public import Mathlib.Data.ZMod.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Original-map consumers of affine quasicoherent base change

These consumers retain the geometric mate, canonical tensor map, adjunction units,
and actual inverse and naturality equations. Nonreduced and zero rings are included.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace QuillenTest.AffineBaseChange


variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]
variable (h : IsPullback
  (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (Spec.map (CommRingCat.ofHom (algebraMap S B)))
  (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (Spec.map (CommRingCat.ofHom (algebraMap R S))))

open scoped TensorProduct ChangeOfRings in
include h in
/-- The scalar map sends every pure tensor through the original coefficient map. -/
theorem original_pure_tensor (M : ModuleCat A) (s : S) (m : M) :
    (ModuleCat.scalarBaseChangeNatTrans R S A B).app M (s ⊗ₜ[R, algebraMap R S] m) =
      algebraMap S B s ⊗ₜ[A, algebraMap A B] m := by
  have := isPushout_of_affineCartesian R S A B h
  exact ModuleCat.scalarBaseChangeMap_tmul R S A B M s m

/-- The actual geometric arrow becomes the canonical tensor cancellation, with fixed comparisons. -/
theorem original_mate_tensor_comparison (M : ModuleCat A) :
    letI := isPushout_of_affineCartesian R S A B h
    (cartesianBaseChangeMap _ _ _ _ h).app (tilde M) ≫
        (affineBaseChangeTargetIso S A B M).hom =
      (affineBaseChangeSourceIso R S A M).hom ≫
        (tilde.functor (CommRingCat.of S)).map
          ((ModuleCat.scalarBaseChangeIsoApp R S A B M).hom) := by
  have := isPushout_of_affineCartesian R S A B h
  rw [affineBaseChangeMap_tilde, ModuleCat.scalarBaseChangeMap_eq_isoApp]

omit [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B] in
/-- The original geometric mate retains the two original adjunction units. -/
theorem original_geometric_unit (M : (Spec (CommRingCat.of A)).Modules) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.app M) ≫
      (cartesianPushforwardSquare _ _ _ _ h).hom.app
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).unit.app
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj M) ≫
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((cartesianBaseChangeMap _ _ _ _ h).app M) :=
  cartesianBaseChangeMap_unit _ _ _ _ h M

/-- The inverse is an inverse of the literal geometric mate on an arbitrary QC sheaf. -/
theorem original_inverse (M : (Spec (CommRingCat.of A)).Modules) [M.IsQuasicoherent] :
    letI := isIso_affineBaseChangeMap R S A B h M
    inv ((cartesianBaseChangeMap _ _ _ _ h).app M) ≫
      (cartesianBaseChangeMap _ _ _ _ h).app M = 𝟙 _ := by
  simp

omit [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B] in
/-- Naturality uses the original pullback and pushforward of an arbitrary sheaf arrow. -/
theorem original_naturality {M N : (Spec (CommRingCat.of A)).Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map φ) ≫
      (cartesianBaseChangeMap _ _ _ _ h).app N =
    (cartesianBaseChangeMap _ _ _ _ h).app M ≫
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap S B)))).map
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map φ) :=
  (cartesianBaseChangeMap _ _ _ _ h).naturality φ

/-- The sheaf comparison identifies the actual geometric unit with the scalar unit. -/
theorem original_tilde_unit {C D : CommRingCat.{u}} (φ : C ⟶ D) (M : ModuleCat C) :
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M) ≫
      (Scheme.Modules.pushforward (Spec.map φ)).map ((tildePullbackIso φ).hom.app M) ≫
      (tildePushforwardIso φ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) =
    (tilde.functor C).map ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M) :=
  tildePullbackIso_unit φ M

/-- Integral coefficients can change to the nonreduced ring ZMod 4 without a flatness premise. -/
theorem nonreduced_coefficient_change (M : (Spec (CommRingCat.of ℤ)).Modules)
    [M.IsQuasicoherent] :
    let h := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout ℤ (ZMod 4) ℤ (ZMod 4)).flip
    IsIso ((cartesianBaseChangeMap _ _ _ _ h).app M) := by
  dsimp only
  exact isIso_affineBaseChangeMap ℤ (ZMod 4) ℤ (ZMod 4) _ M

/-- The same original mate remains invertible after coefficient change to the zero ring. -/
theorem zero_coefficient_change (M : (Spec (CommRingCat.of ℤ)).Modules)
    [M.IsQuasicoherent] :
    let h := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout ℤ (ZMod 1) ℤ (ZMod 1)).flip
    IsIso ((cartesianBaseChangeMap _ _ _ _ h).app M) := by
  dsimp only
  exact isIso_affineBaseChangeMap ℤ (ZMod 1) ℤ (ZMod 1) _ M

end QuillenTest.AffineBaseChange
