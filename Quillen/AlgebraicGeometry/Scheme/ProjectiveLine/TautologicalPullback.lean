/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.RankOne.Pullback
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient

/-! # Pullback charts of the original tautological and quotient lines

The actual chart pullbacks retain the original columns `(1,t)`, `(s,1)` and quotient rows
`(-t,1)`, `(-1,s)` over every commutative base ring.
-/

@[expose] public section
open Quillen


noncomputable section
universe u v u' v'
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- The positive tautological chart, through the original restriction-to-pullback comparison. -/
def tautologicalPullbackPlusIso (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (plusChart R)).obj (tautologicalLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (plusChart R)).symm.app _ ≪≫
    tautologicalLinePlusIso R
/-- The negative tautological chart, through the original restriction-to-pullback comparison. -/
def tautologicalPullbackMinusIso (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (minusChart R)).obj (tautologicalLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (minusChart R)).symm.app _ ≪≫
    tautologicalLineMinusIso R
/-- The positive quotient chart, through the original restriction-to-pullback comparison. -/
def tautologicalQuotientPullbackPlusIso (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (plusChart R)).obj (tautologicalQuotientLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (plusChart R)).symm.app _ ≪≫
    tautologicalQuotientPlusIso R
/-- The negative quotient chart, through the original restriction-to-pullback comparison. -/
def tautologicalQuotientPullbackMinusIso (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (minusChart R)).obj (tautologicalQuotientLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (minusChart R)).symm.app _ ≪≫
    tautologicalQuotientMinusIso R
/-- The genuine positive pullback column is `(1,t)`. -/
theorem tautologicalLineInclusion_pullback_plus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (plusChart R)).map (tautologicalLineInclusion R) ≫
      (pullbackUnitSquareIso (plusChart R)).hom =
      (tautologicalPullbackPlusIso R).hom ≫ graphColumn (unitMul _ (polynomialCoordinate R)) := by
  let e := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (plusChart R)
  apply (cancel_epi (e.hom.app (tautologicalLine R))).mp
  rw [← Category.assoc, ← e.hom.naturality]
  rw [Category.assoc, restrictFunctorIsoPullback_unitSquare]
  rw [tautologicalLineInclusion_plus, Category.assoc,
    firstColumn_unitSquareRestrictionIso]
  simp [tautologicalPullbackPlusIso, e, Category.assoc]
/-- The genuine negative pullback column is `(s,1)`. -/
theorem tautologicalLineInclusion_pullback_minus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (minusChart R)).map (tautologicalLineInclusion R) ≫
      (pullbackUnitSquareIso (minusChart R)).hom =
      (tautologicalPullbackMinusIso R).hom ≫
        cographColumn (unitMul _ (polynomialCoordinate R)) := by
  let e := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (minusChart R)
  apply (cancel_epi (e.hom.app (tautologicalLine R))).mp
  rw [← Category.assoc, ← e.hom.naturality]
  rw [Category.assoc, restrictFunctorIsoPullback_unitSquare]
  rw [tautologicalLineInclusion_minus, Category.assoc,
    secondColumn_unitSquareRestrictionIso]
  simp [tautologicalPullbackMinusIso, e, Category.assoc]
/-- The genuine positive pullback quotient row is `(-t,1)`. -/
theorem tautologicalQuotientMap_pullback_plus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (plusChart R)).map (tautologicalQuotientMap R) ≫
      (tautologicalQuotientPullbackPlusIso R).hom =
      (pullbackUnitSquareIso (plusChart R)).hom ≫
        graphRow (unitMul _ (polynomialCoordinate R)) := by
  let e := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (plusChart R)
  apply (cancel_epi (e.hom.app
    ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
      SheafOfModules.unit (twoChartLine R).ringCatSheaf))).mp
  rw [← Category.assoc, ← e.hom.naturality]
  simp only [tautologicalQuotientPullbackPlusIso, Iso.trans_hom, Category.assoc]
  change _ ≫ e.hom.app _ ≫ e.inv.app _ ≫ (tautologicalQuotientPlusIso R).hom = _
  rw [Iso.hom_inv_id_app_assoc, tautologicalQuotientMap_plus]
  rw [← Category.assoc, restrictFunctorIsoPullback_unitSquare]
  rfl
/-- The genuine negative pullback quotient row is `(-1,s)`. -/
theorem tautologicalQuotientMap_pullback_minus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (minusChart R)).map (tautologicalQuotientMap R) ≫
      (tautologicalQuotientPullbackMinusIso R).hom =
      (pullbackUnitSquareIso (minusChart R)).hom ≫
        cographRow (unitMul _ (polynomialCoordinate R)) := by
  let e := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (minusChart R)
  apply (cancel_epi (e.hom.app
    ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
      SheafOfModules.unit (twoChartLine R).ringCatSheaf))).mp
  rw [← Category.assoc, ← e.hom.naturality]
  simp only [tautologicalQuotientPullbackMinusIso, Iso.trans_hom, Category.assoc]
  change _ ≫ e.hom.app _ ≫ e.inv.app _ ≫ (tautologicalQuotientMinusIso R).hom = _
  rw [Iso.hom_inv_id_app_assoc, tautologicalQuotientMap_minus]
  rw [← Category.assoc, restrictFunctorIsoPullback_unitSquare]
  rfl
end AlgebraicGeometry.Scheme.ProjectiveLine
