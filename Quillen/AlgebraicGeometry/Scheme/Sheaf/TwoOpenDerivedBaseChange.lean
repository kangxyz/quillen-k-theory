/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineCompositeDerivedBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenSheafSequence
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeShift
public import Aglib.CategoryTheory.Triangulated.NatTransIso
public import Quillen.CategoryTheory.Limits.NatTransProduct
public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle
/-! # Flat base change from the original signed two-open triangle -/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived category of module sheaves. -/
local instance twoOpenBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]
/-- An actual affine open chart and its affine composite give the original Čech term comparison. -/
theorem isIso_derivedFlatBaseChangeMap_openLocalization
    {Z : Scheme.{u}} (g : Z ⟶ U) [IsOpenImmersion g]
    [IsAffineHom g] [IsAffineHom (g ≫ f)] (M : U.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj ((openLocalization g).obj M))) :=
  isIso_derivedFlatBaseChangeMap_affinePushforward_single
    (pullback.fst g a) (pullback.snd g a) g a b f j
    (IsPullback.of_hasPullback g a) h (M.restrict g)
/-- The original signed two-open short exact triangle proves flat base change on QC singles. -/
theorem isIso_derivedFlatBaseChangeMap_twoOpen_single
    {O A B : Scheme.{u}} (t : O ⟶ A) (s : O ⟶ B) (iA : A ⟶ U) (iB : B ⟶ U)
    [IsOpenImmersion t] [IsOpenImmersion s] [IsOpenImmersion iA] [IsOpenImmersion iB]
    (hc : IsPullback t s iA iB)
    (hcover : ∀ x : U, (∃ y : A, iA y = x) ∨ (∃ z : B, iB z = x))
    [IsAffineHom iA] [IsAffineHom iB] [IsAffineHom (t ≫ iA)]
    [IsAffineHom (iA ≫ f)] [IsAffineHom (iB ≫ f)] [IsAffineHom ((t ≫ iA) ≫ f)]
    (M : U.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
  let := flat_cartesian_baseChange a b f j h
  let : (derivedPushforwardPlus f).IsTriangulated :=
    inferInstanceAs (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.IsTriangulated
  let : (derivedPushforwardPlus b).IsTriangulated :=
    inferInstanceAs (Scheme.Modules.pushforward b).rightDerivedFunctorPlus.IsTriangulated
  let : (derivedFlatPullbackPlus j).IsTriangulated := by
    unfold derivedFlatPullbackPlus
    infer_instance
  let : (derivedFlatPullbackPlus a).IsTriangulated := by
    unfold derivedFlatPullbackPlus
    infer_instance
  let : (derivedPushforwardPlus f).Additive :=
    inferInstanceAs (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.Additive
  let : (derivedPushforwardPlus b).Additive :=
    inferInstanceAs (Scheme.Modules.pushforward b).rightDerivedFunctorPlus.Additive
  let : (derivedFlatPullbackPlus j).Additive := by
    unfold derivedFlatPullbackPlus
    infer_instance
  let : (derivedFlatPullbackPlus a).Additive := by
    unfold derivedFlatPullbackPlus
    infer_instance
  let F := derivedPushforwardPlus f ⋙ derivedFlatPullbackPlus j
  let G := derivedFlatPullbackPlus a ⋙ derivedPushforwardPlus b
  let α := derivedFlatBaseChangeMap a b f j h
  let := derivedFlatBaseChangeMap_commShift a b f j h
  let hS := TwoOpen.sheafSequence_shortExact t s iA iB hc M hcover
  have h₃ := isIso_derivedFlatBaseChangeMap_openLocalization a b f j h (t ≫ iA) M
  have hA := isIso_derivedFlatBaseChangeMap_openLocalization a b f j h iA M
  have hB := isIso_derivedFlatBaseChangeMap_openLocalization a b f j h iB M
  let : IsIso ((Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor U.Modules 0) α).app
      ((openLocalization iA).obj M)) := hA
  let : IsIso ((Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor U.Modules 0) α).app
      ((openLocalization iB).obj M)) := hB
  have h₂ := NatTrans.isIso_app_prod
    ((DerivedCategory.Plus.singleFunctor U.Modules 0) ⋙ F)
    ((DerivedCategory.Plus.singleFunctor U.Modules 0) ⋙ G)
    (Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor U.Modules 0) α)
    ((openLocalization iA).obj M) ((openLocalization iB).obj M)
  exact isIso₁_of_isIso₂₃ (NatTrans.mapTriangleHom α hS.singleTrianglePlus)
    (F.map_distinguished _ hS.singleTrianglePlus_distinguished)
    (G.map_distinguished _ hS.singleTrianglePlus_distinguished) h₂ h₃
end AlgebraicGeometry.Scheme.Modules
