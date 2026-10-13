/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TwistMinusFunctor
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ModuleColumns

/-!
# The negative twist of the structure module

The canonical kernel twist of the structure module is identified with the original tautological
sheaf by an isomorphism preserving its actual inclusion into the structure-module square.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf Quillen.CoherentScheme
variable (R : CommRingCat.{u})

lemma tautologicalLineInclusion_twistMinusObstruction :
    tautologicalLineInclusion R ≫
      twistMinusObstruction R (SheafOfModules.unit (twoChartLine R).ringCatSheaf) = 0 := by
  apply prod.hom_ext
  · simp only [twistMinusObstruction, Category.assoc, prod.lift_fst, zero_comp]
    apply eq_zero_of_restrict_map_eq_zero (plusChart R) _ ⟨_, ⟨Iso.refl _⟩⟩
    rw [Functor.map_comp, tautologicalLineInclusion_plus]
    have hc := moduleFirstColumn_unit (plusChart R) (polynomialCoordinate R)
    have he : firstColumn (plusChart R) (polynomialCoordinate R) =
        (Scheme.Modules.restrictUnitIso (plusChart R)).inv ≫
          moduleFirstColumn (plusChart R)
            (SheafOfModules.unit (twoChartLine R).ringCatSheaf) (polynomialCoordinate R) := by
      rw [hc, Iso.inv_hom_id_assoc]
    rw [he, Category.assoc, Category.assoc, subobjectObstruction_local_zero, comp_zero,
      comp_zero]
  · simp only [twistMinusObstruction, Category.assoc, prod.lift_snd, zero_comp]
    apply eq_zero_of_restrict_map_eq_zero (minusChart R) _ ⟨_, ⟨Iso.refl _⟩⟩
    rw [Functor.map_comp, tautologicalLineInclusion_minus]
    have hc := moduleSecondColumn_unit (minusChart R) (polynomialCoordinate R)
    have he : secondColumn (minusChart R) (polynomialCoordinate R) =
        (Scheme.Modules.restrictUnitIso (minusChart R)).inv ≫
          moduleSecondColumn (minusChart R)
            (SheafOfModules.unit (twoChartLine R).ringCatSheaf) (polynomialCoordinate R) := by
      rw [hc, Iso.inv_hom_id_assoc]
    rw [he, Category.assoc, Category.assoc, subobjectObstruction_local_zero, comp_zero,
      comp_zero]

/-- The original tautological inclusion factored through the canonical twist kernel. -/
def tautologicalToTwistMinusUnit : tautologicalLine R ⟶
    twistMinus R (SheafOfModules.unit (twoChartLine R).ringCatSheaf) :=
  kernel.lift _ (tautologicalLineInclusion R)
    (tautologicalLineInclusion_twistMinusObstruction R)

lemma tautologicalToTwistMinusUnit_inclusion :
    tautologicalToTwistMinusUnit R ≫ twistMinusInclusion R _ = tautologicalLineInclusion R :=
  kernel.lift_ι _ _ _

lemma tautologicalToTwistMinusUnit_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalToTwistMinusUnit R) ≫
      (twistMinusPlusIso R _).hom =
    (tautologicalLinePlusIso R).hom ≫ (Scheme.Modules.restrictUnitIso (plusChart R)).inv := by
  let := moduleFirstColumn_mono (plusChart R)
    (SheafOfModules.unit (twoChartLine R).ringCatSheaf) (polynomialCoordinate R)
  apply (cancel_mono (moduleFirstColumn (plusChart R)
    (SheafOfModules.unit (twoChartLine R).ringCatSheaf) (polynomialCoordinate R))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (plusChart R)).map
    (tautologicalToTwistMinusUnit_inclusion R)
  rw [Functor.map_comp, twistMinusInclusion_plus, tautologicalLineInclusion_plus] at h
  rw [Category.assoc, h, Category.assoc, moduleFirstColumn_unit,
    Iso.inv_hom_id_assoc]

lemma tautologicalToTwistMinusUnit_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalToTwistMinusUnit R) ≫
      (twistMinusMinusIso R _).hom =
    (tautologicalLineMinusIso R).hom ≫ (Scheme.Modules.restrictUnitIso (minusChart R)).inv := by
  let := moduleSecondColumn_mono (minusChart R)
    (SheafOfModules.unit (twoChartLine R).ringCatSheaf) (polynomialCoordinate R)
  apply (cancel_mono (moduleSecondColumn (minusChart R)
    (SheafOfModules.unit (twoChartLine R).ringCatSheaf) (polynomialCoordinate R))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (minusChart R)).map
    (tautologicalToTwistMinusUnit_inclusion R)
  rw [Functor.map_comp, twistMinusInclusion_minus, tautologicalLineInclusion_minus] at h
  rw [Category.assoc, h, Category.assoc, moduleSecondColumn_unit,
    Iso.inv_hom_id_assoc]

instance tautologicalToTwistMinusUnit_isIso : IsIso (tautologicalToTwistMinusUnit R) := by
  apply isIso_of_restrict_openCover (fun _ : Bool => Spec (.of (Polynomial R)))
    (polynomialChart R) (polynomialChart_cover R)
  intro b
  cases b
  · change IsIso ((Scheme.Modules.restrictFunctor (minusChart R)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (minusChart R)).map
        (tautologicalToTwistMinusUnit R) ≫ (twistMinusMinusIso R _).hom) := by
      rw [tautologicalToTwistMinusUnit_minus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (twistMinusMinusIso R _).hom
  · change IsIso ((Scheme.Modules.restrictFunctor (plusChart R)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (plusChart R)).map
        (tautologicalToTwistMinusUnit R) ≫ (twistMinusPlusIso R _).hom) := by
      rw [tautologicalToTwistMinusUnit_plus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (twistMinusPlusIso R _).hom

/-- The twist of the structure module identified with the original tautological line. -/
def twistMinusUnitIso : twistMinus R (SheafOfModules.unit (twoChartLine R).ringCatSheaf) ≅
    tautologicalLine R := (asIso (tautologicalToTwistMinusUnit R)).symm

lemma twistMinusUnitIso_inclusion :
    (twistMinusUnitIso R).hom ≫ tautologicalLineInclusion R = twistMinusInclusion R _ := by
  rw [← tautologicalToTwistMinusUnit_inclusion, ← Category.assoc]
  exact Iso.inv_hom_id_assoc (asIso (tautologicalToTwistMinusUnit R)) _

end Quillen.Scheme.ProjectiveLine
