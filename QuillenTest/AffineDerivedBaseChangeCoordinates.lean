/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedBaseChangeCoordinates
public import Mathlib.Data.ZMod.Basic

/-! # Original affine derived mate and coordinate consumers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.SchemeSheaf
namespace QuillenTest.AffineDerivedBaseChangeCoordinates

open Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The actual standard derived categories of module sheaves. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {W U V X : Scheme.{u}} [IsAffine W] [IsAffine U] [IsAffine V] [IsAffine X]
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j] (M : U.Modules) [M.IsQuasicoherent]
/-- The actual affine mate has a two-sided inverse on the original single sheaf. -/
theorem original_affine_inverse :
    ∃ r, (derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) ≫ r = 𝟙 _ ∧
      r ≫ (derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) = 𝟙 _ := by
  have := isIso_derivedFlatBaseChangeMap_affine_single a b f j h M
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩
/-- Equality after the original mate detects equality of derived arrows. -/
theorem original_affine_cancellation
    {K : DerivedCategory.Plus V.Modules}
    (q₁ q₂ : K ⟶ (derivedFlatPullbackPlus j).obj
      ((derivedPushforwardPlus f).obj ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)))
    (hq : q₁ ≫ (derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) =
      q₂ ≫ (derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) : q₁ = q₂ := by
  have := isIso_derivedFlatBaseChangeMap_affine_single a b f j h M
  exact (cancel_mono _).mp hq
/-- Coordinate sheaf pullback retains quasicoherence without any noetherian assumption. -/
theorem actual_coordinate_quasicoherence :
    ((Scheme.Modules.pullback U.isoSpec.inv).obj M).IsQuasicoherent :=
  isQuasicoherent_isoSpec_pullback M
include h in
omit [Flat j] in
/-- The coordinate cartesian square retains the literal original maps on global sections. -/
theorem original_coordinate_square :
    Spec.map a.appTop ≫ Spec.map f.appTop = Spec.map b.appTop ≫ Spec.map j.appTop :=
  (specCoordinatePullback a b f j h).w
omit [IsAffine W] [IsAffine U] [IsAffine V] [IsAffine X] [M.IsQuasicoherent] in
/-- The installed composite units still identify the same ordinary base-change mate. -/
theorem original_single_unit_square :
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app (singleZeroPlus U M) ≫
      (derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj (singleZeroPlus U M)) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app
          (singleZeroPlus U M)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback a)
        (Scheme.Modules.pushforward b)).app (singleZeroPlus U M) := by
  let := flat_cartesian_baseChange a b f j h
  exact derivedFlatBaseChangeMap_unit a b f j h (singleZeroPlus U M)
section RingTests
/-- The same original mate retains a two-sided inverse over a nonreduced base ring. -/
theorem nonreduced_original_inverse
    (N : (Spec (CommRingCat.of (ZMod 4))).Modules) [N.IsQuasicoherent] :
    ∃ r, (derivedFlatBaseChangeMap (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) IsPullback.of_id_fst).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ≫ r = 𝟙 _ ∧
      r ≫ (derivedFlatBaseChangeMap (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) IsPullback.of_id_fst).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N) = 𝟙 _ :=
  original_affine_inverse (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) IsPullback.of_id_fst N
/-- The actual zero-ring geometry requires no nontriviality hypothesis. -/
theorem zero_ring_original_inverse
    (N : (Spec (CommRingCat.of (ZMod 1))).Modules) [N.IsQuasicoherent] :
    ∃ r, (derivedFlatBaseChangeMap (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) IsPullback.of_id_fst).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ≫ r = 𝟙 _ ∧
      r ≫ (derivedFlatBaseChangeMap (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) IsPullback.of_id_fst).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N) = 𝟙 _ :=
  original_affine_inverse (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) IsPullback.of_id_fst N
end RingTests
end QuillenTest.AffineDerivedBaseChangeCoordinates
