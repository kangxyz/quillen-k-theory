/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalIncidence
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalPullback
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PullbackSquare

/-! # Four original affine coordinates of diagonal incidence

On the four genuine affine rectangles, the incidence map is scalar multiplication by
`t-u`, `tv-1`, `1-su`, and `v-s`. The chart isomorphisms are obtained from the original
projection squares and retain the original tautological inclusion and quotient maps.
No reducedness or nontriviality hypothesis on the base ring is required.
-/

@[expose] public section

noncomputable section
universe u v u' v'
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf PolynomialLaurent
/-- The original affine-line fiber square over the base ring. -/
def polynomialSquare (R : CommRingCat.{u}) : Scheme.{u} :=
  pullback (polynomialProjection R) (polynomialProjection R)
/-- The original first polynomial projection. -/
def polynomialFirst (R : CommRingCat.{u}) : polynomialSquare R ⟶ Spec (.of (Polynomial R)) :=
  pullback.fst _ _
/-- The original second polynomial projection. -/
def polynomialSecond (R : CommRingCat.{u}) : polynomialSquare R ⟶ Spec (.of (Polynomial R)) :=
  pullback.snd _ _
variable (R : CommRingCat.{u})
    (j k : Spec (.of (Polynomial R)) ⟶ twoChartLine R)
    (hj : j ≫ projection R = polynomialProjection R)
    (hk : k ≫ projection R = polynomialProjection R)
/-- The actual rectangle map induced by two original polynomial charts. -/
def rectangleMap : polynomialSquare R ⟶ relativeSquare R :=
  pullback.map (polynomialProjection R) (polynomialProjection R) (projection R) (projection R)
    j k (𝟙 _) (by simpa only [Category.comp_id] using hj.symm)
      (by simpa only [Category.comp_id] using hk.symm)
instance [IsOpenImmersion j] [IsOpenImmersion k] : IsOpenImmersion (rectangleMap R j k hj hk) := by
  dsimp [rectangleMap]
  infer_instance
@[reassoc (attr := simp)]
theorem rectangleMap_first : rectangleMap R j k hj hk ≫ relativeFirst R = polynomialFirst R ≫ j :=
  by simp [rectangleMap, relativeFirst, polynomialFirst]
@[reassoc (attr := simp)]
theorem rectangleMap_second :
    rectangleMap R j k hj hk ≫ relativeSecond R = polynomialSecond R ≫ k :=
  by simp [rectangleMap, relativeSecond, polynomialSecond]
/-- The first original chart's tautological trivialization on the actual rectangle. -/
def rectangleLineIso
    (e : (AlgebraicGeometry.Scheme.Modules.pullback j).obj (tautologicalLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj (tautologicalLine R)) ≅
      SheafOfModules.unit (polynomialSquare R).ringCatSheaf :=
  (pullbackSquareIso (rectangleMap R j k hj hk) (relativeFirst R) (polynomialFirst R) j
      (rectangleMap_first R j k hj hk)).app _ ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (polynomialFirst R)).mapIso e ≪≫
      pullbackUnitIso (polynomialFirst R)
/-- The second original chart's quotient trivialization on the actual rectangle. -/
def rectangleQuotientIso
    (e : (AlgebraicGeometry.Scheme.Modules.pullback k).obj (tautologicalQuotientLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeSecond R)).obj
          (tautologicalQuotientLine R)) ≅ SheafOfModules.unit (polynomialSquare R).ringCatSheaf :=
  (pullbackSquareIso (rectangleMap R j k hj hk) (relativeSecond R) (polynomialSecond R) k
      (rectangleMap_second R j k hj hk)).app _ ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (polynomialSecond R)).mapIso e ≪≫
      pullbackUnitIso (polynomialSecond R)
/-- Actual rectangle transport retains a given original chart column. -/
theorem rectangleLine_column
    (e : (AlgebraicGeometry.Scheme.Modules.pullback j).obj (tautologicalLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (C : (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :
      (Spec (.of (Polynomial R))).Modules) ⟶ _)
    (D : (SheafOfModules.unit (polynomialSquare R).ringCatSheaf :
      (polynomialSquare R).Modules) ⟶ _)
    (he : (AlgebraicGeometry.Scheme.Modules.pullback j).map (tautologicalLineInclusion R) ≫
      (pullbackUnitSquareIso j).hom = e.hom ≫ C)
    (hC : (AlgebraicGeometry.Scheme.Modules.pullback (polynomialFirst R)).map C ≫
      (pullbackUnitSquareIso (polynomialFirst R)).hom =
      (pullbackUnitIso (polynomialFirst R)).hom ≫ D) :
    (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).map
          (tautologicalLineInclusion R)) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        (pullbackUnitSquareIso (relativeFirst R)).hom ≫
      (pullbackUnitSquareIso (rectangleMap R j k hj hk)).hom =
        (rectangleLineIso R j k hj hk e).hom ≫ D := by
  rw [pullbackSquareIso_map_to_unitSquare (rectangleMap R j k hj hk) (relativeFirst R)
    (polynomialFirst R) j (rectangleMap_first R j k hj hk), he]
  rw [Functor.map_comp, Category.assoc, hC]
  rfl
/-- Actual rectangle transport retains a given original quotient row. -/
theorem rectangleQuotient_row
    (e : (AlgebraicGeometry.Scheme.Modules.pullback k).obj (tautologicalQuotientLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (C : _ ⟶ (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :
      (Spec (.of (Polynomial R))).Modules))
    (D : _ ⟶ (SheafOfModules.unit (polynomialSquare R).ringCatSheaf :
      (polynomialSquare R).Modules))
    (he : (AlgebraicGeometry.Scheme.Modules.pullback k).map (tautologicalQuotientMap R) ≫
      e.hom = (pullbackUnitSquareIso k).hom ≫ C)
    (hC : (AlgebraicGeometry.Scheme.Modules.pullback (polynomialSecond R)).map C ≫
      (pullbackUnitIso (polynomialSecond R)).hom =
      (pullbackUnitSquareIso (polynomialSecond R)).hom ≫ D) :
    (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeSecond R)).map
          (tautologicalQuotientMap R)) ≫ (rectangleQuotientIso R j k hj hk e).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        (pullbackUnitSquareIso (relativeSecond R)).hom ≫
      (pullbackUnitSquareIso (rectangleMap R j k hj hk)).hom ≫ D := by
  change _ ≫ (pullbackSquareIso (rectangleMap R j k hj hk) (relativeSecond R)
      (polynomialSecond R) k (rectangleMap_second R j k hj hk)).hom.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (polynomialSecond R)).map e.hom ≫
        (pullbackUnitIso (polynomialSecond R)).hom = _
  rw [pullbackSquareIso_map_from_unitSquare, he, Functor.map_comp, Category.assoc, hC]
  have h := congrArg (fun z => z ≫ D)
    (pullbackSquareIso_unitSquare (rectangleMap R j k hj hk) (relativeSecond R)
      (polynomialSecond R) k (rectangleMap_second R j k hj hk))
  simpa only [Category.assoc] using h
/-- Incidence transport uses the original chart column and quotient row in their given order. -/
theorem diagonalIncidence_rectangle
    (e : (AlgebraicGeometry.Scheme.Modules.pullback j).obj (tautologicalLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (q : (AlgebraicGeometry.Scheme.Modules.pullback k).obj (tautologicalQuotientLine R) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (C : (SheafOfModules.unit (polynomialSquare R).ringCatSheaf :
      (polynomialSquare R).Modules) ⟶ _)
    (D : _ ⟶ (SheafOfModules.unit (polynomialSquare R).ringCatSheaf :
      (polynomialSquare R).Modules))
    (hC : (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).map
          (tautologicalLineInclusion R)) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        (pullbackUnitSquareIso (relativeFirst R)).hom ≫
      (pullbackUnitSquareIso (rectangleMap R j k hj hk)).hom =
        (rectangleLineIso R j k hj hk e).hom ≫ C)
    (hD : (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeSecond R)).map
          (tautologicalQuotientMap R)) ≫ (rectangleQuotientIso R j k hj hk q).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        (pullbackUnitSquareIso (relativeSecond R)).hom ≫
      (pullbackUnitSquareIso (rectangleMap R j k hj hk)).hom ≫ D) :
    (AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)).map
        (diagonalIncidence R) ≫ (rectangleQuotientIso R j k hj hk q).hom =
      (rectangleLineIso R j k hj hk e).hom ≫ C ≫ D := by
  let F := AlgebraicGeometry.Scheme.Modules.pullback (rectangleMap R j k hj hk)
  simp only [diagonalIncidence, Functor.map_comp, Category.assoc]
  rw [hD]
  change F.map _ ≫ F.map _ ≫ F.map _ ≫ F.map _ ≫ _ = _
  rw [← F.map_comp_assoc (pullbackUnitSquareIso (relativeSecond R)).inv
      (pullbackUnitSquareIso (relativeSecond R)).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ D) hC
end Quillen.Scheme.ProjectiveLine

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf PolynomialLaurent
/-- The actual first polynomial coordinate on the affine rectangle. -/
def rectangleFirstCoordinate (R : CommRingCat.{u}) : Γ(polynomialSquare R, ⊤) :=
  (polynomialFirst R).appTop.hom (polynomialCoordinate R)
/-- The actual second polynomial coordinate on the affine rectangle. -/
def rectangleSecondCoordinate (R : CommRingCat.{u}) : Γ(polynomialSquare R, ⊤) :=
  (polynomialSecond R).appTop.hom (polynomialCoordinate R)
/-- The literal incidence scalar on the plus-plus rectangle. -/
theorem diagonalIncidence_plus_plus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (rectangleMap R (plusChart R) (plusChart R) (plusChart_projection R)
        (plusChart_projection R))).map (diagonalIncidence R) ≫
        (rectangleQuotientIso R (plusChart R) (plusChart R)
          (plusChart_projection R) (plusChart_projection R)
          (tautologicalQuotientPullbackPlusIso R)).hom =
      (rectangleLineIso R (plusChart R) (plusChart R) (plusChart_projection R)
        (plusChart_projection R)
        (tautologicalPullbackPlusIso R)).hom ≫
        unitMul (polynomialSquare R)
          (rectangleFirstCoordinate R - rectangleSecondCoordinate R) := by
  have h := diagonalIncidence_rectangle
    R (plusChart R)
    (plusChart R) (plusChart_projection R) (plusChart_projection R)
    (tautologicalPullbackPlusIso R) (tautologicalQuotientPullbackPlusIso R)
    (graphColumn (unitMul _ (rectangleFirstCoordinate R)))
    (graphRow (unitMul _ (rectangleSecondCoordinate R)))
    (rectangleLine_column R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R)
      (tautologicalPullbackPlusIso R) _ _
      (tautologicalLineInclusion_pullback_plus R)
      (graphColumn_pullback (polynomialFirst R) (polynomialCoordinate R)))
    (rectangleQuotient_row R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R)
      (tautologicalQuotientPullbackPlusIso R) _ _
      (tautologicalQuotientMap_pullback_plus R)
      (graphRow_pullback (polynomialSecond R) (polynomialCoordinate R)))
  rw [graphColumn_graphRow_unitMul] at h
  exact h
/-- The literal incidence scalar on the plus-minus rectangle. -/
theorem diagonalIncidence_plus_minus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (rectangleMap R (plusChart R) (minusChart R) (plusChart_projection R)
        (minusChart_projection R))).map (diagonalIncidence R) ≫
        (rectangleQuotientIso R (plusChart R) (minusChart R)
          (plusChart_projection R) (minusChart_projection R)
          (tautologicalQuotientPullbackMinusIso R)).hom =
      (rectangleLineIso R (plusChart R) (minusChart R) (plusChart_projection R)
        (minusChart_projection R)
        (tautologicalPullbackPlusIso R)).hom ≫
        unitMul (polynomialSquare R)
          (rectangleFirstCoordinate R * rectangleSecondCoordinate R - 1) := by
  have h := diagonalIncidence_rectangle
    R (plusChart R)
    (minusChart R) (plusChart_projection R) (minusChart_projection R)
    (tautologicalPullbackPlusIso R) (tautologicalQuotientPullbackMinusIso R)
    (graphColumn (unitMul _ (rectangleFirstCoordinate R)))
    (cographRow (unitMul _ (rectangleSecondCoordinate R)))
    (rectangleLine_column R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R)
      (tautologicalPullbackPlusIso R) _ _
      (tautologicalLineInclusion_pullback_plus R)
      (graphColumn_pullback (polynomialFirst R) (polynomialCoordinate R)))
    (rectangleQuotient_row R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R)
      (tautologicalQuotientPullbackMinusIso R) _ _
      (tautologicalQuotientMap_pullback_minus R)
      (cographRow_pullback (polynomialSecond R) (polynomialCoordinate R)))
  rw [graphColumn_cographRow_unitMul] at h
  exact h
/-- The literal incidence scalar on the minus-plus rectangle. -/
theorem diagonalIncidence_minus_plus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (rectangleMap R (minusChart R) (plusChart R) (minusChart_projection R)
        (plusChart_projection R))).map (diagonalIncidence R) ≫
        (rectangleQuotientIso R (minusChart R) (plusChart R)
          (minusChart_projection R) (plusChart_projection R)
          (tautologicalQuotientPullbackPlusIso R)).hom =
      (rectangleLineIso R (minusChart R) (plusChart R) (minusChart_projection R)
        (plusChart_projection R)
        (tautologicalPullbackMinusIso R)).hom ≫
        unitMul (polynomialSquare R)
          (1 - rectangleFirstCoordinate R * rectangleSecondCoordinate R) := by
  have h := diagonalIncidence_rectangle
    R (minusChart R)
    (plusChart R) (minusChart_projection R) (plusChart_projection R)
    (tautologicalPullbackMinusIso R) (tautologicalQuotientPullbackPlusIso R)
    (cographColumn (unitMul _ (rectangleFirstCoordinate R)))
    (graphRow (unitMul _ (rectangleSecondCoordinate R)))
    (rectangleLine_column R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R)
      (tautologicalPullbackMinusIso R) _ _
      (tautologicalLineInclusion_pullback_minus R)
      (cographColumn_pullback (polynomialFirst R) (polynomialCoordinate R)))
    (rectangleQuotient_row R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R)
      (tautologicalQuotientPullbackPlusIso R) _ _
      (tautologicalQuotientMap_pullback_plus R)
      (graphRow_pullback (polynomialSecond R) (polynomialCoordinate R)))
  rw [cographColumn_graphRow_unitMul] at h
  exact h
/-- The literal incidence scalar on the minus-minus rectangle. -/
theorem diagonalIncidence_minus_minus (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (rectangleMap R (minusChart R) (minusChart R) (minusChart_projection R)
        (minusChart_projection R))).map (diagonalIncidence R) ≫
        (rectangleQuotientIso R (minusChart R) (minusChart R)
          (minusChart_projection R) (minusChart_projection R)
          (tautologicalQuotientPullbackMinusIso R)).hom =
      (rectangleLineIso R (minusChart R) (minusChart R)
        (minusChart_projection R) (minusChart_projection R)
        (tautologicalPullbackMinusIso R)).hom ≫
        unitMul (polynomialSquare R)
          (rectangleSecondCoordinate R - rectangleFirstCoordinate R) := by
  have h := diagonalIncidence_rectangle
    R (minusChart R)
    (minusChart R) (minusChart_projection R) (minusChart_projection R)
    (tautologicalPullbackMinusIso R) (tautologicalQuotientPullbackMinusIso R)
    (cographColumn (unitMul _ (rectangleFirstCoordinate R)))
    (cographRow (unitMul _ (rectangleSecondCoordinate R)))
    (rectangleLine_column R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R)
      (tautologicalPullbackMinusIso R) _ _
      (tautologicalLineInclusion_pullback_minus R)
      (cographColumn_pullback (polynomialFirst R) (polynomialCoordinate R)))
    (rectangleQuotient_row R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R)
      (tautologicalQuotientPullbackMinusIso R) _ _
      (tautologicalQuotientMap_pullback_minus R)
      (cographRow_pullback (polynomialSecond R) (polynomialCoordinate R)))
  rw [cographColumn_cographRow_unitMul] at h
  exact h
end Quillen.Scheme.ProjectiveLine
