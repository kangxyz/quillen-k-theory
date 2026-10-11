/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalTensorPushforward
public import Mathlib.Data.ZMod.Basic

/-!
# Original-map consumers of the ordinary projection formula

Inspect the geometric unit, both naturality variables and literal cartesian
open-base-change square. Unique lifting uses the original projection arrow.
The original diagonal and negative line give geometric consumers, including
nonreduced and zero base rings.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModulesOfCommRing
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
namespace Quillen.Tests.VectorBundleProjectionFormula

/-- The comparison on the structure module retains the original geometric unit. -/
theorem original_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    projectionFormulaMap f (SheafOfModules.unit Y.ringCatSheaf) M ≫
      (Scheme.Modules.pushforward f).map
        ((moduleTensorRightFunctor X M).map (pullbackUnitIso f).hom ≫
          (tensorLeftUnitIso X.sheaf).hom.app M) =
      (tensorLeftUnitIso Y.sheaf).hom.app ((Scheme.Modules.pushforward f).obj M) :=
  projectionFormulaMap_unit f M

/-- An arbitrary coefficient arrow retains the actual pullback and pushforward maps. -/
theorem original_coefficient_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {E E' : Y.Modules} (g : E ⟶ E') (M : X.Modules) :
    (moduleTensorCoefficientMap Y g).app ((Scheme.Modules.pushforward f).obj M) ≫
        projectionFormulaMap f E' M =
      projectionFormulaMap f E M ≫ (Scheme.Modules.pushforward f).map
        ((moduleTensorCoefficientMap X ((Scheme.Modules.pullback f).map g)).app M) :=
  (projectionFormulaNatTrans f M).naturality g

/-- Naturality in the source module uses the original second tensor factor. -/
theorem original_module_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) {M N : X.Modules} (g : M ⟶ N) :
    (moduleTensorLeftFunctor Y E).map ((Scheme.Modules.pushforward f).map g) ≫
        projectionFormulaMap f E N =
      projectionFormulaMap f E M ≫ (Scheme.Modules.pushforward f).map
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).map g) :=
  projectionFormulaMap_naturality f E g

/-- The actual cartesian square retains its original open comparisons and pullback mate. -/
theorem original_open_base_change {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
    (E : X.Modules) (M : U.Modules) :
    (tensorRestrictionIso j E ((Scheme.Modules.pushforward f).obj M)).hom ≫
      (Scheme.Modules.restrictFunctor j).map (projectionFormulaMap f E M) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        ((moduleTensorLeftFunctor U ((Scheme.Modules.pullback f).obj E)).obj M) =
    (moduleTensorLeftFunctor V (E.restrict j)).map
        ((cartesianOpenBaseChange a b f j h).hom.app M) ≫
      projectionFormulaMap b (E.restrict j) (M.restrict a) ≫
      (Scheme.Modules.pushforward b).map
        ((moduleTensorCoefficientMap W
          ((cartesianPullbackBaseChangeMate a b f j h).app E)).app (M.restrict a) ≫
          (tensorRestrictionIso a ((Scheme.Modules.pullback f).obj E) M).hom) :=
  projectionFormulaMap_openBaseChange a b f j h E M

/-- Every arrow into the original target lifts uniquely through the original projection map. -/
theorem unique_original_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [IsFiniteLocallyFree Y E] (M : X.Modules) (N : Y.Modules)
    (h : N ⟶ (Scheme.Modules.pushforward f).obj
      ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M)) :
    ∃! g : N ⟶ (moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M),
      g ≫ projectionFormulaMap f E M = h := by
  let e := projectionFormulaIso f E M
  change ∃! g : N ⟶ (moduleTensorLeftFunctor Y E).obj
    ((Scheme.Modules.pushforward f).obj M), g ≫ e.hom = h
  refine ⟨h ≫ e.inv, by simp, ?_⟩
  intro g hg
  apply (cancel_mono e.hom).mp
  simpa using hg

/-- Tensor on the diagonal retains the original section-pullback identification. -/
theorem original_diagonal_negative (R : CommRingCat.{u}) :
    (diagonalTensorPushforwardIso R (tautologicalLine R) (tautologicalQuotientLine R)).hom =
      projectionFormulaMap (relativeDiagonal R)
        ((Scheme.Modules.pullback (relativeFirst R)).obj (tautologicalLine R))
        (tautologicalQuotientLine R) ≫
      (Scheme.Modules.pushforward (relativeDiagonal R)).map
        ((moduleTensorCoefficientMap (twoChartLine R)
          ((sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
            (relativeDiagonal_first R)).hom.app (tautologicalLine R))).app
              (tautologicalQuotientLine R)) :=
  diagonalTensorPushforwardIso_hom R _ _

/-- The original diagonal identification remains invertible over a nonreduced ring. -/
theorem nonreduced_diagonal :
    IsIso (diagonalTensorPushforwardIso (CommRingCat.of (ZMod 4))
      (tautologicalLine (CommRingCat.of (ZMod 4)))
      (tautologicalQuotientLine (CommRingCat.of (ZMod 4)))).hom := inferInstance

/-- The same original diagonal identification includes the zero ring. -/
theorem zero_ring_diagonal :
    IsIso (diagonalTensorPushforwardIso (CommRingCat.of (ZMod 1))
      (tautologicalLine (CommRingCat.of (ZMod 1)))
      (tautologicalQuotientLine (CommRingCat.of (ZMod 1)))).hom := inferInstance

end Quillen.Tests.VectorBundleProjectionFormula
