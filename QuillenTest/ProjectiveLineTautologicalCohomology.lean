/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalCohomology
public import Mathlib.Data.ZMod.Basic

/-! Original signed sections, unique chart preimages, global sections, and injective cocycles. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf.TwoOpen Quillen.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineTautologicalCohomology

open Quillen

/-- Every original intersection section has a unique original pair of chart preimages. -/
theorem unique_chart_pair (R : CommRingCat.{u})
    (z : Γ(tautologicalLine R, (plusChart R).opensRange ⊓ (minusChart R).opensRange)) :
    ∃! x : Γ(tautologicalLine R, (plusChart R).opensRange) ×
        Γ(tautologicalLine R, (minusChart R).opensRange),
      difference (tautologicalLine R) (plusChart R).opensRange (minusChart R).opensRange x = z := by
  obtain ⟨x, hx⟩ := tautological_difference_surjective R z
  exact ⟨x, hx, fun y hy => tautological_difference_injective R (hy.trans hx.symm)⟩

/-- The original signed restriction kernel is zero in both actual chart coordinates. -/
theorem original_difference_eq_zero (R : CommRingCat.{u})
    (a : Γ(tautologicalLine R, (plusChart R).opensRange))
    (b : Γ(tautologicalLine R, (minusChart R).opensRange)) :
    difference (tautologicalLine R) (plusChart R).opensRange (minusChart R).opensRange (a, b) = 0 ↔
      a = 0 ∧ b = 0 := by
  rw [map_eq_zero_iff _ (tautological_difference_injective R)]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- An actual global section vanishes, rather than only its derived image. -/
theorem original_global_section_zero (R : CommRingCat.{u}) (s : Γ(tautologicalLine R, ⊤)) :
    s = 0 := by
  have h := (IsZero.iff_id_eq_zero _).mp (isZero_globalSections_tautologicalLine R)
  exact congrArg (fun f => AddCommGrpCat.Hom.hom f s) h

/-- The cocycle belongs to the original arbitrary ambient injective resolution. -/
theorem original_degree_one_boundary (R : CommRingCat.{u})
    (I : InjectiveResolution (tautologicalLine R))
    (z : Γ(I.cocomplex.X 1, ⊤)) (hz : (I.cocomplex.d 1 2).app ⊤ z = 0) :
    ∃ y : Γ(I.cocomplex.X 0, ⊤), (I.cocomplex.d 0 1).app ⊤ y = z := by
  have h : (((sectionsFunctor (twoChartLine R) ⊤).mapHomologicalComplex _).obj
      I.cocomplex).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (isZero_rightDerived_tautologicalLine_one R).of_iso
      (I.isoRightDerivedObj (sectionsFunctor (twoChartLine R) ⊤) 1).symm
  have h' := (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp h
  exact (ShortComplex.ab_exact_iff _).mp h' z hz

/-- Actual degree-zero derived maps vanish as well. -/
theorem original_degree_zero_map (R : CommRingCat.{u}) (A : AddCommGrpCat.{u})
    (f : A ⟶ ((sectionsFunctor (twoChartLine R) ⊤).rightDerived 0).obj (tautologicalLine R)) :
    f = 0 :=
  (isZero_rightDerived_tautologicalLine R 0).eq_of_tgt _ _

/-- The conclusion ranges over every original right-derived degree. -/
theorem original_all_degree_map (R : CommRingCat.{u}) (n : ℕ) (A : AddCommGrpCat.{u})
    (f : ((sectionsFunctor (twoChartLine R) ⊤).rightDerived n).obj (tautologicalLine R) ⟶ A) :
    f = 0 :=
  (isZero_rightDerived_tautologicalLine R n).eq_of_src _ _

/-- Nonreduced rings retain the actual first-degree conclusion. -/
theorem nonreduced_base :
    IsZero (((sectionsFunctor (twoChartLine (.of (ZMod 4))) ⊤).rightDerived 1).obj
      (tautologicalLine (.of (ZMod 4)))) :=
  isZero_rightDerived_tautologicalLine (.of (ZMod 4)) 1

/-- The zero ring is included in every degree. -/
theorem zero_base (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine (.of (ZMod 1))) ⊤).rightDerived n).obj
      (tautologicalLine (.of (ZMod 1)))) :=
  isZero_rightDerived_tautologicalLine (.of (ZMod 1)) n

end QuillenTest.ProjectiveLineTautologicalCohomology
