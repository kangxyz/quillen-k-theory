/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PullbackUnit
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient

/-! # The original relative diagonal incidence complex

On the genuine relative fiber product, the incidence map goes from the first pullback
of the tautological line to the second pullback of the quotient line. Its pullback along
the original diagonal is zero. Adjunction supplies the actual map to the diagonal
pushforward of the quotient line and the resulting short complex. Exactness is not asserted.
-/

@[expose] public section

noncomputable section
universe u v u' v'
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
/-- The original relative fiber square of the two-chart line. -/
def relativeSquare (R : CommRingCat.{u}) : Scheme.{u} :=
  pullback (projection R) (projection R)
/-- The original first projection. -/
def relativeFirst (R : CommRingCat.{u}) : relativeSquare R ⟶ twoChartLine R :=
  pullback.fst _ _
/-- The original second projection. -/
def relativeSecond (R : CommRingCat.{u}) : relativeSquare R ⟶ twoChartLine R :=
  pullback.snd _ _
/-- The actual relative diagonal, given by the fiber-product universal property. -/
def relativeDiagonal (R : CommRingCat.{u}) : twoChartLine R ⟶ relativeSquare R :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)
@[reassoc (attr := simp)]
theorem relativeDiagonal_first (R : CommRingCat.{u}) :
    relativeDiagonal R ≫ relativeFirst R = 𝟙 _ := pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem relativeDiagonal_second (R : CommRingCat.{u}) :
    relativeDiagonal R ≫ relativeSecond R = 𝟙 _ := pullback.lift_snd _ _ _
/-- The incidence map from the original tautological subline to the original quotient line. -/
def diagonalIncidence (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj (tautologicalLine R) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (relativeSecond R)).obj
        (tautologicalQuotientLine R) :=
  (AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).map (tautologicalLineInclusion R) ≫
    (pullbackUnitSquareIso (relativeFirst R)).hom ≫
      (pullbackUnitSquareIso (relativeSecond R)).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (relativeSecond R)).map (tautologicalQuotientMap R)
/-- The actual incidence map vanishes after pullback along the original relative diagonal. -/
theorem diagonalIncidence_pullback_diagonal (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (relativeDiagonal R)).map (diagonalIncidence R) = 0 := by
  let F := AlgebraicGeometry.Scheme.Modules.pullback (relativeDiagonal R)
  let e₁ := sectionPullbackIso (relativeDiagonal R) (relativeFirst R) (relativeDiagonal_first R)
  let e₂ := sectionPullbackIso (relativeDiagonal R) (relativeSecond R) (relativeDiagonal_second R)
  apply (cancel_mono (e₂.hom.app (tautologicalQuotientLine R))).mp
  rw [zero_comp]
  change F.map (diagonalIncidence R) ≫ e₂.hom.app (tautologicalQuotientLine R) = 0
  simp only [diagonalIncidence, Functor.map_comp, Category.assoc]
  rw [show F.map ((AlgebraicGeometry.Scheme.Modules.pullback (relativeSecond R)).map
      (tautologicalQuotientMap R)) ≫ e₂.hom.app (tautologicalQuotientLine R) =
      e₂.hom.app ((SheafOfModules.unit (twoChartLine R).ringCatSheaf :
          (twoChartLine R).Modules) ⨯ SheafOfModules.unit (twoChartLine R).ringCatSheaf) ≫
        tautologicalQuotientMap R from e₂.hom.naturality _]
  dsimp only [e₂]
  rw [sectionPullbackIso_unitSquare]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc (pullbackUnitSquareIso (relativeSecond R)).inv
      (pullbackUnitSquareIso (relativeSecond R)).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc _ (pullbackUnitSquareIso (relativeDiagonal R)).hom,
    ← sectionPullbackIso_unitSquare (relativeDiagonal R) (relativeFirst R)
      (relativeDiagonal_first R)]
  change (F.map ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).map
      (tautologicalLineInclusion R)) ≫ e₁.hom.app
        ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
          SheafOfModules.unit (twoChartLine R).ringCatSheaf)) ≫ tautologicalQuotientMap R = 0
  rw [show F.map ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).map
      (tautologicalLineInclusion R)) ≫ e₁.hom.app
        ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
          SheafOfModules.unit (twoChartLine R).ringCatSheaf) =
      e₁.hom.app (tautologicalLine R) ≫ tautologicalLineInclusion R from e₁.hom.naturality _]
  simp only [Category.assoc, tautologicalQuotientMap, cokernel.condition,
    comp_zero]
/-- The actual adjoint quotient map to the diagonal direct image of the original quotient line. -/
def diagonalQuotientMap (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullback (relativeSecond R)).obj
        (tautologicalQuotientLine R) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).obj
        (tautologicalQuotientLine R) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (relativeDiagonal R)).homEquiv _ _
    ((sectionPullbackIso (relativeDiagonal R) (relativeSecond R)
      (relativeDiagonal_second R)).hom.app (tautologicalQuotientLine R))
/-- The two original diagonal maps compose to zero. -/
theorem diagonalIncidence_quotient (R : CommRingCat.{u}) :
    diagonalIncidence R ≫ diagonalQuotientMap R = 0 := by
  rw [diagonalQuotientMap, ← Adjunction.homEquiv_naturality_left,
    diagonalIncidence_pullback_diagonal, zero_comp]
  simp [Adjunction.homEquiv_apply]
/-- The original incidence and diagonal adjoint quotient as a short complex. -/
def diagonalIncidenceSequence (R : CommRingCat.{u}) :
    ShortComplex (relativeSquare R).Modules :=
  ShortComplex.mk (diagonalIncidence R) (diagonalQuotientMap R) (diagonalIncidence_quotient R)
end Quillen.Scheme.ProjectiveLine
