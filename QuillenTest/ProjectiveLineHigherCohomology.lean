/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Cohomology
public import Mathlib.Data.ZMod.Basic

/-! A degree-two cocycle in the original global sections of an arbitrary
injective resolution is an actual boundary. Higher derived global-section
objects have no nonzero incoming morphisms, including over a nonreduced base
and the zero ring. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf.TwoOpen Quillen.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineHigherCohomology

open Quillen

lemma degree_two_cocycle_is_boundary (R : CommRingCat.{u})
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent] (I : InjectiveResolution M)
    (z : Γ(I.cocomplex.X 2, ⊤)) (hz : (I.cocomplex.d 2 3).app ⊤ z = 0) :
    ∃ y : Γ(I.cocomplex.X 1, ⊤), (I.cocomplex.d 1 2).app ⊤ y = z := by
  have h := injectiveResolution_sections_exact_add_two R M I 0
  have h' := (HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp)).mp h
  exact (ShortComplex.ab_exact_iff _).mp h' z hz

lemma higher_cohomology_map_zero (R : CommRingCat.{u})
    (M : (twoChartLine R).Modules) [M.IsQuasicoherent] (n : ℕ) (A : AddCommGrpCat.{u})
    (f : A ⟶ ((sectionsFunctor (twoChartLine R) ⊤).rightDerived (n + 2)).obj M) : f = 0 :=
  (isZero_rightDerived_globalSections_add_two R M n).eq_of_tgt _ _

example (M : (twoChartLine (.of (ZMod 4))).Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) (z : Γ(I.cocomplex.X 2, ⊤))
    (hz : (I.cocomplex.d 2 3).app ⊤ z = 0) :
    ∃ y : Γ(I.cocomplex.X 1, ⊤), (I.cocomplex.d 1 2).app ⊤ y = z :=
  degree_two_cocycle_is_boundary (.of (ZMod 4)) M I z hz

example (M : (twoChartLine (.of (ZMod 1))).Modules) [M.IsQuasicoherent] :
    IsZero (((sectionsFunctor (twoChartLine (.of (ZMod 1))) ⊤).rightDerived 2).obj M) :=
  isZero_rightDerived_globalSections_add_two (.of (ZMod 1)) M 0

end QuillenTest.ProjectiveLineHigherCohomology
