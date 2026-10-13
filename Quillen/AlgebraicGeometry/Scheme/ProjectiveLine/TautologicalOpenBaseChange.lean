/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OpenBaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RankOneRestriction
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TwistMinusUnit

/-!
# The original tautological line under open coefficient change

The actual restriction of the tautological line along open coefficient change is identified with
the original tautological line over the changed ring. Both chart isomorphisms come from literal
restriction squares. The global comparison is factored through the canonical twist kernel and
preserves the original inclusion into the unit square.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.Scheme.ProjectiveLine
open Quillen.PolynomialBaseChange Quillen.SchemeSheaf
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

lemma polynomialMap_coordinate :
    (Spec.map (polynomialMap f)).appTop.hom (polynomialCoordinate R) =
      polynomialCoordinate S := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial S))).hom).1
  have h := congrArg (fun k => CommRingCat.Hom.hom k (polynomialCoordinate R))
    (Scheme.ΓSpecIso_naturality (polynomialMap f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  simpa [polynomialCoordinate, polynomialMap] using h

variable [IsOpenImmersion (Spec.map f)]
instance polynomialMap_open : IsOpenImmersion (Spec.map (polynomialMap f)) :=
  MorphismProperty.of_isPullback (polynomialProjection_isPullback f) inferInstance

/-- Positive-chart trivialization of the actual restricted tautological line. -/
def tautologicalOpenPlusIso :
    ((tautologicalLine R).restrict (coefficientMap f)).restrict (plusChart S) ≅
      SheafOfModules.unit (Spec (.of (Polynomial S))).ringCatSheaf :=
  restrictionSquareLineIso (plusChart S) (coefficientMap f) (Spec.map (polynomialMap f))
    (plusChart R) (plusChart_coefficientMap f) _ (tautologicalLinePlusIso R)

/-- Negative-chart trivialization of the actual restricted tautological line. -/
def tautologicalOpenMinusIso :
    ((tautologicalLine R).restrict (coefficientMap f)).restrict (minusChart S) ≅
      SheafOfModules.unit (Spec (.of (Polynomial S))).ringCatSheaf :=
  restrictionSquareLineIso (minusChart S) (coefficientMap f) (Spec.map (polynomialMap f))
    (minusChart R) (minusChart_coefficientMap f) _ (tautologicalLineMinusIso R)

/-- The restricted original tautological inclusion transported to the original unit square. -/
def tautologicalOpenInclusion : (tautologicalLine R).restrict (coefficientMap f) ⟶
    ((SheafOfModules.unit (twoChartLine S).ringCatSheaf : (twoChartLine S).Modules) ⨯
      SheafOfModules.unit (twoChartLine S).ringCatSheaf) :=
  (Scheme.Modules.restrictFunctor (coefficientMap f)).map (tautologicalLineInclusion R) ≫
    (unitSquareRestrictionIso (coefficientMap f)).hom

lemma tautologicalOpenInclusion_plus :
    (Scheme.Modules.restrictFunctor (plusChart S)).map (tautologicalOpenInclusion f) =
      (tautologicalOpenPlusIso f).hom ≫ firstColumn (plusChart S) (polynomialCoordinate S) := by
  simpa only [polynomialMap_coordinate, tautologicalOpenInclusion, tautologicalOpenPlusIso] using
    restrictionSquare_firstColumn (plusChart S) (coefficientMap f)
      (Spec.map (polynomialMap f)) (plusChart R) (plusChart_coefficientMap f)
      (tautologicalLine R) (tautologicalLinePlusIso R) (tautologicalLineInclusion R)
      (polynomialCoordinate R) (tautologicalLineInclusion_plus R)

lemma tautologicalOpenInclusion_minus :
    (Scheme.Modules.restrictFunctor (minusChart S)).map (tautologicalOpenInclusion f) =
      (tautologicalOpenMinusIso f).hom ≫ secondColumn (minusChart S) (polynomialCoordinate S) := by
  simpa only [polynomialMap_coordinate, tautologicalOpenInclusion, tautologicalOpenMinusIso] using
    restrictionSquare_secondColumn (minusChart S) (coefficientMap f)
      (Spec.map (polynomialMap f)) (minusChart R) (minusChart_coefficientMap f)
      (tautologicalLine R) (tautologicalLineMinusIso R) (tautologicalLineInclusion R)
      (polynomialCoordinate R) (tautologicalLineInclusion_minus R)

end Quillen.Scheme.ProjectiveLine

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf Quillen.CoherentScheme
variable {R S : CommRingCat.{u}} (f : R ⟶ S) [IsOpenImmersion (Spec.map f)]

lemma tautologicalOpenInclusion_obstruction :
    tautologicalOpenInclusion f ≫
      twistMinusObstruction S (SheafOfModules.unit (twoChartLine S).ringCatSheaf) = 0 := by
  apply prod.hom_ext
  · simp only [twistMinusObstruction, Category.assoc, prod.lift_fst, zero_comp]
    apply eq_zero_of_restrict_map_eq_zero (plusChart S) _ ⟨_, ⟨Iso.refl _⟩⟩
    rw [Functor.map_comp, tautologicalOpenInclusion_plus]
    have hc := moduleFirstColumn_unit (plusChart S) (polynomialCoordinate S)
    have he : firstColumn (plusChart S) (polynomialCoordinate S) =
        (Scheme.Modules.restrictUnitIso (plusChart S)).inv ≫
          moduleFirstColumn (plusChart S)
            (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S) := by
      rw [hc, Iso.inv_hom_id_assoc]
    rw [he, Category.assoc, Category.assoc, subobjectObstruction_local_zero, comp_zero,
      comp_zero]
  · simp only [twistMinusObstruction, Category.assoc, prod.lift_snd, zero_comp]
    apply eq_zero_of_restrict_map_eq_zero (minusChart S) _ ⟨_, ⟨Iso.refl _⟩⟩
    rw [Functor.map_comp, tautologicalOpenInclusion_minus]
    have hc := moduleSecondColumn_unit (minusChart S) (polynomialCoordinate S)
    have he : secondColumn (minusChart S) (polynomialCoordinate S) =
        (Scheme.Modules.restrictUnitIso (minusChart S)).inv ≫
          moduleSecondColumn (minusChart S)
            (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S) := by
      rw [hc, Iso.inv_hom_id_assoc]
    rw [he, Category.assoc, Category.assoc, subobjectObstruction_local_zero, comp_zero,
      comp_zero]

/-- The original restricted inclusion factored through the canonical twist kernel. -/
def tautologicalOpenToTwistUnit : ((tautologicalLine R).restrict (coefficientMap f)) ⟶
    twistMinus S (SheafOfModules.unit (twoChartLine S).ringCatSheaf) :=
  kernel.lift _ (tautologicalOpenInclusion f)
    (tautologicalOpenInclusion_obstruction f)

lemma tautologicalOpenToTwistUnit_inclusion :
    tautologicalOpenToTwistUnit f ≫ twistMinusInclusion S _ = tautologicalOpenInclusion f :=
  kernel.lift_ι _ _ _

lemma tautologicalOpenToTwistUnit_plus :
    (Scheme.Modules.restrictFunctor (plusChart S)).map (tautologicalOpenToTwistUnit f) ≫
      (twistMinusPlusIso S _).hom =
    (tautologicalOpenPlusIso f).hom ≫ (Scheme.Modules.restrictUnitIso (plusChart S)).inv := by
  let := moduleFirstColumn_mono (plusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S)
  apply (cancel_mono (moduleFirstColumn (plusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (plusChart S)).map
    (tautologicalOpenToTwistUnit_inclusion f)
  rw [Functor.map_comp, twistMinusInclusion_plus, tautologicalOpenInclusion_plus] at h
  rw [Category.assoc, h, Category.assoc, moduleFirstColumn_unit,
    Iso.inv_hom_id_assoc]

lemma tautologicalOpenToTwistUnit_minus :
    (Scheme.Modules.restrictFunctor (minusChart S)).map (tautologicalOpenToTwistUnit f) ≫
      (twistMinusMinusIso S _).hom =
    (tautologicalOpenMinusIso f).hom ≫ (Scheme.Modules.restrictUnitIso (minusChart S)).inv := by
  let := moduleSecondColumn_mono (minusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S)
  apply (cancel_mono (moduleSecondColumn (minusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (minusChart S)).map
    (tautologicalOpenToTwistUnit_inclusion f)
  rw [Functor.map_comp, twistMinusInclusion_minus, tautologicalOpenInclusion_minus] at h
  rw [Category.assoc, h, Category.assoc, moduleSecondColumn_unit,
    Iso.inv_hom_id_assoc]

instance tautologicalOpenToTwistUnit_isIso : IsIso (tautologicalOpenToTwistUnit f) := by
  apply isIso_of_restrict_openCover (fun _ : Bool => Spec (.of (Polynomial S)))
    (polynomialChart S) (polynomialChart_cover S)
  intro b
  cases b
  · change IsIso ((Scheme.Modules.restrictFunctor (minusChart S)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (minusChart S)).map
        (tautologicalOpenToTwistUnit f) ≫ (twistMinusMinusIso S _).hom) := by
      rw [tautologicalOpenToTwistUnit_minus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (twistMinusMinusIso S _).hom
  · change IsIso ((Scheme.Modules.restrictFunctor (plusChart S)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (plusChart S)).map
        (tautologicalOpenToTwistUnit f) ≫ (twistMinusPlusIso S _).hom) := by
      rw [tautologicalOpenToTwistUnit_plus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (twistMinusPlusIso S _).hom

/-- Open coefficient restriction identified with the original changed-base tautological line. -/
def tautologicalOpenIso : (tautologicalLine R).restrict (coefficientMap f) ≅
    tautologicalLine S :=
  asIso (tautologicalOpenToTwistUnit f) ≪≫ twistMinusUnitIso S

lemma tautologicalOpenIso_inclusion :
    (tautologicalOpenIso f).hom ≫ tautologicalLineInclusion S =
      tautologicalOpenInclusion f := by
  simp only [tautologicalOpenIso, Iso.trans_hom, Category.assoc]
  rw [twistMinusUnitIso_inclusion]
  exact tautologicalOpenToTwistUnit_inclusion f

lemma tautologicalOpenIso_plus :
    (Scheme.Modules.restrictFunctor (plusChart S)).map (tautologicalOpenIso f).hom ≫
      (tautologicalLinePlusIso S).hom = (tautologicalOpenPlusIso f).hom := by
  let := firstColumn_mono (plusChart S) (polynomialCoordinate S)
  apply (cancel_mono (firstColumn (plusChart S) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (plusChart S)).map
    (tautologicalOpenIso_inclusion f)
  rw [Functor.map_comp, tautologicalLineInclusion_plus, tautologicalOpenInclusion_plus] at h
  simpa only [Category.assoc] using h

lemma tautologicalOpenIso_minus :
    (Scheme.Modules.restrictFunctor (minusChart S)).map (tautologicalOpenIso f).hom ≫
      (tautologicalLineMinusIso S).hom = (tautologicalOpenMinusIso f).hom := by
  let := secondColumn_mono (minusChart S) (polynomialCoordinate S)
  apply (cancel_mono (secondColumn (minusChart S) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (minusChart S)).map
    (tautologicalOpenIso_inclusion f)
  rw [Functor.map_comp, tautologicalLineInclusion_minus, tautologicalOpenInclusion_minus] at h
  simpa only [Category.assoc] using h

end Quillen.Scheme.ProjectiveLine
