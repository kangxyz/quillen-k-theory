/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalOpenBaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalPullback
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PullbackSquare
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PullbackRankOne
public import Aglib.AlgebraicGeometry.Modules.Restriction.ZeroMorphisms
public import Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing

/-!
# Actual tautological pullback under arbitrary coefficient change

No flatness or open-immersion premise is imposed on the coefficient map.
The original chart columns construct the line comparison through the actual
kernel presentation, retaining both original trivializations and inclusion.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent


open ModuleCat
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Coherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.ProjectiveLine
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Actual positive pullback-chart trivialization. -/
def tautologicalCoefficientPlusPullbackIso :
    (Scheme.Modules.pullback (plusChart S)).obj
        ((Scheme.Modules.pullback (coefficientMap f)).obj (tautologicalLine R)) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Polynomial S))).ringCatSheaf :=
  (pullbackSquareIso (plusChart S) (coefficientMap f) (Spec.map (polynomialMap f))
      (plusChart R) (plusChart_coefficientMap f)).app _ ≪≫
    (Scheme.Modules.pullback (Spec.map (polynomialMap f))).mapIso
      (tautologicalPullbackPlusIso R) ≪≫ pullbackUnitIso (Spec.map (polynomialMap f))

/-- Actual negative pullback-chart trivialization. -/
def tautologicalCoefficientMinusPullbackIso :
    (Scheme.Modules.pullback (minusChart S)).obj
        ((Scheme.Modules.pullback (coefficientMap f)).obj (tautologicalLine R)) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Polynomial S))).ringCatSheaf :=
  (pullbackSquareIso (minusChart S) (coefficientMap f) (Spec.map (polynomialMap f))
      (minusChart R) (minusChart_coefficientMap f)).app _ ≪≫
    (Scheme.Modules.pullback (Spec.map (polynomialMap f))).mapIso
      (tautologicalPullbackMinusIso R) ≪≫ pullbackUnitIso (Spec.map (polynomialMap f))

/-- The pulled-back original inclusion in the ordered actual target unit square. -/
def tautologicalCoefficientInclusion :
    (Scheme.Modules.pullback (coefficientMap f)).obj (tautologicalLine R) ⟶
      ((SheafOfModules.unit (twoChartLine S).ringCatSheaf : (twoChartLine S).Modules) ⨯
        SheafOfModules.unit (twoChartLine S).ringCatSheaf) :=
  (Scheme.Modules.pullback (coefficientMap f)).map (tautologicalLineInclusion R) ≫
    (pullbackUnitSquareIso (coefficientMap f)).hom

lemma tautologicalCoefficientPlusPullbackColumn :
    (Scheme.Modules.pullback (plusChart S)).map (tautologicalCoefficientInclusion f) ≫
        (pullbackUnitSquareIso (plusChart S)).hom =
      (tautologicalCoefficientPlusPullbackIso f).hom ≫
        graphColumn (unitMul _ (polynomialCoordinate S)) := by
  dsimp only [tautologicalCoefficientInclusion]
  rw [Functor.map_comp, Category.assoc,
    pullbackSquareIso_map_to_unitSquare (plusChart S) (coefficientMap f)
      (Spec.map (polynomialMap f)) (plusChart R) (plusChart_coefficientMap f)]
  rw [tautologicalLineInclusion_pullback_plus, Functor.map_comp, Category.assoc,
    graphColumn_pullback, polynomialMap_coordinate]
  rfl

lemma tautologicalCoefficientMinusPullbackColumn :
    (Scheme.Modules.pullback (minusChart S)).map (tautologicalCoefficientInclusion f) ≫
        (pullbackUnitSquareIso (minusChart S)).hom =
      (tautologicalCoefficientMinusPullbackIso f).hom ≫
        cographColumn (unitMul _ (polynomialCoordinate S)) := by
  dsimp only [tautologicalCoefficientInclusion]
  rw [Functor.map_comp, Category.assoc,
    pullbackSquareIso_map_to_unitSquare (minusChart S) (coefficientMap f)
      (Spec.map (polynomialMap f)) (minusChart R) (minusChart_coefficientMap f)]
  rw [tautologicalLineInclusion_pullback_minus, Functor.map_comp, Category.assoc,
    cographColumn_pullback, polynomialMap_coordinate]
  rfl

/-- Positive restriction chart, through the actual restriction-to-pullback map. -/
def tautologicalCoefficientPlusIso :
    ((Scheme.Modules.pullback (coefficientMap f)).obj (tautologicalLine R)).restrict
        (plusChart S) ≅ SheafOfModules.unit (Spec (CommRingCat.of (Polynomial S))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (plusChart S)).app _ ≪≫
    tautologicalCoefficientPlusPullbackIso f

/-- Negative restriction chart, with the original inverse-coordinate chart. -/
def tautologicalCoefficientMinusIso :
    ((Scheme.Modules.pullback (coefficientMap f)).obj (tautologicalLine R)).restrict
        (minusChart S) ≅ SheafOfModules.unit (Spec (CommRingCat.of (Polynomial S))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (minusChart S)).app _ ≪≫
    tautologicalCoefficientMinusPullbackIso f

lemma tautologicalCoefficientInclusion_plus :
    (Scheme.Modules.restrictFunctor (plusChart S)).map (tautologicalCoefficientInclusion f) =
      (tautologicalCoefficientPlusIso f).hom ≫
        firstColumn (plusChart S) (polynomialCoordinate S) := by
  apply (cancel_mono (unitSquareRestrictionIso (plusChart S)).hom).mp
  rw [Category.assoc, firstColumn_unitSquareRestrictionIso,
    ← restrictFunctorIsoPullback_unitSquare, ← Category.assoc,
    (Scheme.Modules.restrictFunctorIsoPullback (plusChart S)).hom.naturality,
    Category.assoc, tautologicalCoefficientPlusPullbackColumn]
  rfl

lemma tautologicalCoefficientInclusion_minus :
    (Scheme.Modules.restrictFunctor (minusChart S)).map (tautologicalCoefficientInclusion f) =
      (tautologicalCoefficientMinusIso f).hom ≫
        secondColumn (minusChart S) (polynomialCoordinate S) := by
  apply (cancel_mono (unitSquareRestrictionIso (minusChart S)).hom).mp
  rw [Category.assoc, secondColumn_unitSquareRestrictionIso,
    ← restrictFunctorIsoPullback_unitSquare, ← Category.assoc,
    (Scheme.Modules.restrictFunctorIsoPullback (minusChart S)).hom.naturality,
    Category.assoc, tautologicalCoefficientMinusPullbackColumn]
  rfl

end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

lemma tautologicalCoefficientInclusion_obstruction :
    tautologicalCoefficientInclusion f ≫
      twistMinusObstruction S (SheafOfModules.unit (twoChartLine S).ringCatSheaf) = 0 := by
  apply prod.hom_ext
  · simp only [twistMinusObstruction, Category.assoc, prod.lift_fst, zero_comp]
    apply AlgebraicGeometry.Scheme.Modules.eq_zero_of_restrict_map_eq_zero (plusChart S) _ ⟨_,
      ⟨Iso.refl _⟩⟩
    rw [Functor.map_comp, tautologicalCoefficientInclusion_plus]
    have hc := moduleFirstColumn_unit (plusChart S) (polynomialCoordinate S)
    have he : firstColumn (plusChart S) (polynomialCoordinate S) =
        (Scheme.Modules.restrictUnitIso (plusChart S)).inv ≫
          moduleFirstColumn (plusChart S)
            (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S) := by
      rw [hc, Iso.inv_hom_id_assoc]
    rw [he, Category.assoc, Category.assoc,
      AlgebraicGeometry.Scheme.Modules.subobjectObstruction_local_zero, comp_zero,
      comp_zero]
  · simp only [twistMinusObstruction, Category.assoc, prod.lift_snd, zero_comp]
    apply AlgebraicGeometry.Scheme.Modules.eq_zero_of_restrict_map_eq_zero (minusChart S) _ ⟨_,
      ⟨Iso.refl _⟩⟩
    rw [Functor.map_comp, tautologicalCoefficientInclusion_minus]
    have hc := moduleSecondColumn_unit (minusChart S) (polynomialCoordinate S)
    have he : secondColumn (minusChart S) (polynomialCoordinate S) =
        (Scheme.Modules.restrictUnitIso (minusChart S)).inv ≫
          moduleSecondColumn (minusChart S)
            (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S) := by
      rw [hc, Iso.inv_hom_id_assoc]
    rw [he, Category.assoc, Category.assoc,
      AlgebraicGeometry.Scheme.Modules.subobjectObstruction_local_zero, comp_zero,
      comp_zero]

/-- The original pulled-back inclusion factored through the canonical twist kernel. -/
def tautologicalCoefficientToTwistUnit :
    (Scheme.Modules.pullback (coefficientMap f)).obj (tautologicalLine R) ⟶
    twistMinus S (SheafOfModules.unit (twoChartLine S).ringCatSheaf) :=
  kernel.lift _ (tautologicalCoefficientInclusion f)
    (tautologicalCoefficientInclusion_obstruction f)

lemma tautologicalCoefficientToTwistUnit_inclusion :
    tautologicalCoefficientToTwistUnit f ≫ twistMinusInclusion S _ =
      tautologicalCoefficientInclusion f :=
  kernel.lift_ι _ _ _

lemma tautologicalCoefficientToTwistUnit_plus :
    (Scheme.Modules.restrictFunctor (plusChart S)).map (tautologicalCoefficientToTwistUnit f) ≫
      (twistMinusPlusIso S _).hom =
    (tautologicalCoefficientPlusIso f).hom ≫
      (Scheme.Modules.restrictUnitIso (plusChart S)).inv := by
  let := moduleFirstColumn_mono (plusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S)
  apply (cancel_mono (moduleFirstColumn (plusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (plusChart S)).map
    (tautologicalCoefficientToTwistUnit_inclusion f)
  rw [Functor.map_comp, twistMinusInclusion_plus, tautologicalCoefficientInclusion_plus] at h
  rw [Category.assoc, h, Category.assoc, moduleFirstColumn_unit,
    Iso.inv_hom_id_assoc]

lemma tautologicalCoefficientToTwistUnit_minus :
    (Scheme.Modules.restrictFunctor (minusChart S)).map (tautologicalCoefficientToTwistUnit f) ≫
      (twistMinusMinusIso S _).hom =
    (tautologicalCoefficientMinusIso f).hom ≫
      (Scheme.Modules.restrictUnitIso (minusChart S)).inv := by
  let := moduleSecondColumn_mono (minusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S)
  apply (cancel_mono (moduleSecondColumn (minusChart S)
    (SheafOfModules.unit (twoChartLine S).ringCatSheaf) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (minusChart S)).map
    (tautologicalCoefficientToTwistUnit_inclusion f)
  rw [Functor.map_comp, twistMinusInclusion_minus, tautologicalCoefficientInclusion_minus] at h
  rw [Category.assoc, h, Category.assoc, moduleSecondColumn_unit,
    Iso.inv_hom_id_assoc]

instance tautologicalCoefficientToTwistUnit_isIso :
    IsIso (tautologicalCoefficientToTwistUnit f) := by
  apply isIso_of_restrict_openCover (fun _ : Bool => Spec (.of (Polynomial S)))
    (polynomialChart S) (polynomialChart_cover S)
  intro b
  cases b
  · change IsIso ((Scheme.Modules.restrictFunctor (minusChart S)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (minusChart S)).map
        (tautologicalCoefficientToTwistUnit f) ≫ (twistMinusMinusIso S _).hom) := by
      rw [tautologicalCoefficientToTwistUnit_minus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (twistMinusMinusIso S _).hom
  · change IsIso ((Scheme.Modules.restrictFunctor (plusChart S)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (plusChart S)).map
        (tautologicalCoefficientToTwistUnit f) ≫ (twistMinusPlusIso S _).hom) := by
      rw [tautologicalCoefficientToTwistUnit_plus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (twistMinusPlusIso S _).hom

/-- Arbitrary coefficient pullback identified with the original changed-base tautological line. -/
def tautologicalCoefficientIso :
    (Scheme.Modules.pullback (coefficientMap f)).obj (tautologicalLine R) ≅
    tautologicalLine S :=
  asIso (tautologicalCoefficientToTwistUnit f) ≪≫ twistMinusUnitIso S

lemma tautologicalCoefficientIso_inclusion :
    (tautologicalCoefficientIso f).hom ≫ tautologicalLineInclusion S =
      tautologicalCoefficientInclusion f := by
  simp only [tautologicalCoefficientIso, Iso.trans_hom, Category.assoc]
  rw [twistMinusUnitIso_inclusion]
  exact tautologicalCoefficientToTwistUnit_inclusion f

lemma tautologicalCoefficientIso_plus :
    (Scheme.Modules.restrictFunctor (plusChart S)).map (tautologicalCoefficientIso f).hom ≫
      (tautologicalLinePlusIso S).hom = (tautologicalCoefficientPlusIso f).hom := by
  let := firstColumn_mono (plusChart S) (polynomialCoordinate S)
  apply (cancel_mono (firstColumn (plusChart S) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (plusChart S)).map
    (tautologicalCoefficientIso_inclusion f)
  rw [Functor.map_comp, tautologicalLineInclusion_plus, tautologicalCoefficientInclusion_plus] at h
  simpa only [Category.assoc] using h

lemma tautologicalCoefficientIso_minus :
    (Scheme.Modules.restrictFunctor (minusChart S)).map (tautologicalCoefficientIso f).hom ≫
      (tautologicalLineMinusIso S).hom = (tautologicalCoefficientMinusIso f).hom := by
  let := secondColumn_mono (minusChart S) (polynomialCoordinate S)
  apply (cancel_mono (secondColumn (minusChart S) (polynomialCoordinate S))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (minusChart S)).map
    (tautologicalCoefficientIso_inclusion f)
  rw [Functor.map_comp, tautologicalLineInclusion_minus,
    tautologicalCoefficientInclusion_minus] at h
  simpa only [Category.assoc] using h

end AlgebraicGeometry.Scheme.ProjectiveLine
