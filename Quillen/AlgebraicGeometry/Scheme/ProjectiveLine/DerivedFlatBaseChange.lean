/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.TwoOpen
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalIncidence
/-! # Actual flat base change of the two-chart projective-line projection

The canonical derived mate is invertible on each quasicoherent single sheaf over every
commutative base ring. The comparison uses the original fiber product, projections and
installed single-pullback unit. No coefficient-perfection or generation claim is made.
-/

@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
/-- The standard derived category of module sheaves. -/
local instance projectiveFlatBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})
/-- The literal projection mate is invertible under every flat base change on QC singles. -/
theorem isIso_derivedProjectionBaseChange_single
    {W V : Scheme.{u}} (a : W ⟶ twoChartLine R) (b : W ⟶ V) (j : V ⟶ Spec R)
    (h : IsPullback a b (projection R) j) [Flat j]
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap a b (projection R) j h).app
      ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) :=
  isIso_derivedFlatBaseChangeMap_twoOpen_single a b (projection R) j h
    (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R)
    (chart_isPullback R) (charts_jointly_surjective R) M
/-- Projection base change retains the original mate followed by the literal single pullback. -/
def derivedProjectionBaseChangeSingleIso
    {W V : Scheme.{u}} (a : W ⟶ twoChartLine R) (b : W ⟶ V) (j : V ⟶ Spec R)
    (h : IsPullback a b (projection R) j) [Flat j]
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent] :
    letI := flat_cartesian_baseChange a b (projection R) j h
    (derivedFlatPullbackPlus j).obj
      ((derivedPushforwardPlus (projection R)).obj
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) ≅
    (derivedPushforwardPlus b).obj
      ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pullback a).obj M)) := by
  let := flat_cartesian_baseChange a b (projection R) j h
  have := isIso_derivedProjectionBaseChange_single R a b j h M
  exact asIso ((derivedFlatBaseChangeMap a b (projection R) j h).app
      ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) ≪≫
    (derivedPushforwardPlus b).mapIso (derivedFlatPullbackPlusSingleIso a M)
/-- The comparison hom is the original canonical mate followed by the installed
single comparison. -/
theorem derivedProjectionBaseChangeSingleIso_hom
    {W V : Scheme.{u}} (a : W ⟶ twoChartLine R) (b : W ⟶ V) (j : V ⟶ Spec R)
    (h : IsPullback a b (projection R) j) [Flat j]
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent] :
    letI := flat_cartesian_baseChange a b (projection R) j h
    (derivedProjectionBaseChangeSingleIso R a b j h M).hom =
      (derivedFlatBaseChangeMap a b (projection R) j h).app
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M) ≫
        (derivedPushforwardPlus b).map (derivedFlatPullbackPlusSingleIso a M).hom := rfl
/-- The self-base-change comparison uses the original fiber product and its two projections. -/
def derivedSelfBaseChangeSingleIso (M : (twoChartLine R).Modules) [M.IsQuasicoherent] :
    (derivedFlatPullbackPlus (projection R)).obj
      ((derivedPushforwardPlus (projection R)).obj
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) ≅
    (derivedPushforwardPlus (relativeSecond R)).obj
      ((DerivedCategory.Plus.singleFunctor (relativeSquare R).Modules 0).obj
        ((Scheme.Modules.pullback (relativeFirst R)).obj M)) :=
  derivedProjectionBaseChangeSingleIso R (relativeFirst R) (relativeSecond R) (projection R)
    (IsPullback.of_hasPullback (projection R) (projection R)) M
end AlgebraicGeometry.Scheme.ProjectiveLine
