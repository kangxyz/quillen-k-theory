/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedFlatBaseChange
public import Mathlib.Data.ZMod.Basic

/-! # Original projective-line mate, signed differential, and connecting-map consumers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.SchemeSheaf
open Quillen.Scheme.ProjectiveLine Quillen.Scheme.PolynomialLaurent
namespace QuillenTest.ProjectiveLineDerivedFlatBaseChange

open Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The actual standard module-sheaf derived categories. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) [M.IsQuasicoherent]
/-- An arbitrary flat cartesian base change gives an inverse to the literal projection mate. -/
theorem original_projection_mate_inverse
    {W V : Scheme.{u}} (a : W ⟶ twoChartLine R) (b : W ⟶ V) (j : V ⟶ Spec R)
    (h : IsPullback a b (projection R) j) [Flat j] :
    ∃ r, (derivedFlatBaseChangeMap a b (projection R) j h).app
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M) ≫ r = 𝟙 _ ∧
      r ≫ (derivedFlatBaseChangeMap a b (projection R) j h).app
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M) = 𝟙 _ := by
  have := isIso_derivedProjectionBaseChange_single R a b j h M
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩
/-- The original self-base-change hom retains both the actual mate and its single-pullback map. -/
theorem original_self_comparison_hom :
    letI := flat_cartesian_baseChange (relativeFirst R) (relativeSecond R)
      (projection R) (projection R) (IsPullback.of_hasPullback _ _)
    (derivedSelfBaseChangeSingleIso R M).hom =
      (derivedFlatBaseChangeMap (relativeFirst R) (relativeSecond R)
          (projection R) (projection R) (IsPullback.of_hasPullback _ _)).app
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M) ≫
        (derivedPushforwardPlus (relativeSecond R)).map
          (derivedFlatPullbackPlusSingleIso (relativeFirst R) M).hom := rfl
omit [M.IsQuasicoherent] in
/-- The same canonical mate commutes with the original signed restriction differential. -/
theorem original_signed_difference :
    letI := flat_cartesian_baseChange (relativeFirst R) (relativeSecond R)
      (projection R) (projection R) (IsPullback.of_hasPullback _ _)
    let α := derivedFlatBaseChangeMap (relativeFirst R) (relativeSecond R)
      (projection R) (projection R) (IsPullback.of_hasPullback _ _)
    let q := (DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).map
      (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
        (plusChart R) (minusChart R) (overlap_equation R) M)
    (derivedPushforwardPlus (projection R) ⋙ derivedFlatPullbackPlus (projection R)).map q ≫
      α.app _ = α.app _ ≫
        (derivedFlatPullbackPlus (relativeFirst R) ⋙
          derivedPushforwardPlus (relativeSecond R)).map q := by
  exact (derivedFlatBaseChangeMap (relativeFirst R) (relativeSecond R)
    (projection R) (projection R) (IsPullback.of_hasPullback _ _)).naturality _
omit [M.IsQuasicoherent] in
/-- The actual short-exact connecting morphism is retained by the original canonical mate. -/
theorem original_connecting_morphism :
    letI := flat_cartesian_baseChange (relativeFirst R) (relativeSecond R)
      (projection R) (projection R) (IsPullback.of_hasPullback _ _)
    let α := derivedFlatBaseChangeMap (relativeFirst R) (relativeSecond R)
      (projection R) (projection R) (IsPullback.of_hasPullback _ _)
    let T := (TwoOpen.sheafSequence_shortExact (laurentPlus R) (laurentMinus R)
      (plusChart R) (minusChart R) (chart_isPullback R) M
      (charts_jointly_surjective R)).singleTrianglePlus
    (derivedPushforwardPlus (projection R) ⋙ derivedFlatPullbackPlus (projection R)).map T.mor₃ ≫
        α.app _ = α.app _ ≫
      (derivedFlatPullbackPlus (relativeFirst R) ⋙
        derivedPushforwardPlus (relativeSecond R)).map T.mor₃ := by
  exact (derivedFlatBaseChangeMap (relativeFirst R) (relativeSecond R)
    (projection R) (projection R) (IsPullback.of_hasPullback _ _)).naturality _
/-- Self-base-change retains a two-sided inverse over a nonreduced base ring. -/
theorem nonreduced_self_inverse
    (N : (twoChartLine (CommRingCat.of (ZMod 4))).Modules) [N.IsQuasicoherent] :
    (derivedSelfBaseChangeSingleIso (CommRingCat.of (ZMod 4)) N).hom ≫
      (derivedSelfBaseChangeSingleIso (CommRingCat.of (ZMod 4)) N).inv = 𝟙 _ :=
  (derivedSelfBaseChangeSingleIso (CommRingCat.of (ZMod 4)) N).hom_inv_id
/-- The original self-base-change comparison also applies to the zero ring. -/
theorem zero_ring_self_inverse
    (N : (twoChartLine (CommRingCat.of (ZMod 1))).Modules) [N.IsQuasicoherent] :
    (derivedSelfBaseChangeSingleIso (CommRingCat.of (ZMod 1)) N).inv ≫
      (derivedSelfBaseChangeSingleIso (CommRingCat.of (ZMod 1)) N).hom = 𝟙 _ :=
  (derivedSelfBaseChangeSingleIso (CommRingCat.of (ZMod 1)) N).inv_hom_id
end QuillenTest.ProjectiveLineDerivedFlatBaseChange
