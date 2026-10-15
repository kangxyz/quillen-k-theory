/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.StructureSheafCohomology
public import Mathlib.Data.ZMod.Basic

/-! Consumers of actual signed section compatibility and positive derived
structure-sheaf vanishing, including nonreduced and zero base rings. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.TwoOpen AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineStructureSheafCohomology

open Quillen

lemma signed_chart_difference_zero_iff (R : CommRingCat.{u})
    (a : Γ(SheafOfModules.unit (twoChartLine R).ringCatSheaf, (plusChart R).opensRange))
    (b : Γ(SheafOfModules.unit (twoChartLine R).ringCatSheaf, (minusChart R).opensRange)) :
    difference (SheafOfModules.unit (twoChartLine R).ringCatSheaf)
      (plusChart R).opensRange (minusChart R).opensRange (a, b) = 0 ↔
    chartSectionsDifference R
      ((IsOpenImmersion.ΓIsoTop (plusChart R)).inv.hom a,
       (IsOpenImmersion.ΓIsoTop (minusChart R)).inv.hom b) = 0 := by
  rw [← structureSheaf_difference_coordinates]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (overlapSectionsIso R).inv).1).symm

lemma degree_one_cocycle_is_boundary (R : CommRingCat.{u})
    (I : InjectiveResolution (show (twoChartLine R).Modules from
      SheafOfModules.unit (twoChartLine R).ringCatSheaf))
    (z : Γ(I.cocomplex.X 1, ⊤)) (hz : (I.cocomplex.d 1 2).app ⊤ z = 0) :
    ∃ y : Γ(I.cocomplex.X 0, ⊤), (I.cocomplex.d 0 1).app ⊤ y = z := by
  have h : (((sectionsFunctor (twoChartLine R) ⊤).mapHomologicalComplex _).obj
      I.cocomplex).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (isZero_rightDerived_structureSheaf_one R).of_iso
      (I.isoRightDerivedObj (sectionsFunctor (twoChartLine R) ⊤) 1).symm
  have h' := (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp h
  exact (ShortComplex.ab_exact_iff _).mp h' z hz

lemma first_cohomology_map_zero (R : CommRingCat.{u}) (A : AddCommGrpCat.{u})
    (f : A ⟶ ((sectionsFunctor (twoChartLine R) ⊤).rightDerived 1).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) : f = 0 :=
  (isZero_rightDerived_structureSheaf_one R).eq_of_tgt _ _

lemma positive_cohomology_map_zero (R : CommRingCat.{u}) (n : ℕ) (A : AddCommGrpCat.{u})
    (f : A ⟶ ((sectionsFunctor (twoChartLine R) ⊤).rightDerived (n + 1)).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) : f = 0 :=
  (isZero_rightDerived_structureSheaf_succ R n).eq_of_tgt _ _

example : IsZero (((sectionsFunctor (twoChartLine (.of (ZMod 4))) ⊤).rightDerived 1).obj
    (SheafOfModules.unit (twoChartLine (.of (ZMod 4))).ringCatSheaf)) :=
  isZero_rightDerived_structureSheaf_one (.of (ZMod 4))

example (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine (.of (ZMod 1))) ⊤).rightDerived (n + 1)).obj
      (SheafOfModules.unit (twoChartLine (.of (ZMod 1))).ringCatSheaf)) :=
  isZero_rightDerived_structureSheaf_succ (.of (ZMod 1)) n

end QuillenTest.ProjectiveLineStructureSheafCohomology
