/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotientCohomology
public import Mathlib.Data.ZMod.Basic

/-! Actual quotient projection, coefficient sections and original injective-resolution cocycles. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf.TwoOpen Quillen.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineTautologicalQuotientCohomology

open Quillen

/-- Every quotient section has a unique lift along the original global quotient map. -/
theorem original_global_lift (R : CommRingCat.{u}) (z : Γ(tautologicalQuotientLine R, ⊤)) :
    ∃! w : Γ(((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
      SheafOfModules.unit (twoChartLine R).ringCatSheaf), ⊤),
      (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤).hom w = z := by
  have h := ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤)
  obtain ⟨w, hw⟩ := h.2 z
  exact ⟨w, hw, fun v hv => h.1 (hv.trans hw.symm)⟩

/-- The actual quotient section has unique coordinates in two copies of the base ring. -/
theorem original_coefficient_pair (R : CommRingCat.{u}) (z : Γ(tautologicalQuotientLine R, ⊤)) :
    ∃! p : R × R, (tautologicalQuotientGlobalSectionsIso R).hom.hom p = z := by
  have h := ConcreteCategory.bijective_of_isIso (tautologicalQuotientGlobalSectionsIso R).hom
  obtain ⟨p, hp⟩ := h.2 z
  exact ⟨p, hp, fun q hq => h.1 (hq.trans hp.symm)⟩

/-- The two-coefficient section is evaluated through the literal original quotient map. -/
theorem original_coefficient_projection (R : CommRingCat.{u}) (p : R × R) :
    (tautologicalQuotientGlobalSectionsIso R).hom.hom p =
      (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤).hom
        ((unitSquareGlobalSectionsIso R).hom.hom p) := rfl

/-- The cocycle belongs to the original arbitrary ambient injective resolution. -/
theorem original_degree_one_boundary (R : CommRingCat.{u})
    (I : InjectiveResolution (tautologicalQuotientLine R))
    (z : Γ(I.cocomplex.X 1, ⊤)) (hz : (I.cocomplex.d 1 2).app ⊤ z = 0) :
    ∃ y : Γ(I.cocomplex.X 0, ⊤), (I.cocomplex.d 0 1).app ⊤ y = z := by
  have h : (((sectionsFunctor (twoChartLine R) ⊤).mapHomologicalComplex _).obj
      I.cocomplex).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (isZero_rightDerived_tautologicalQuotientLine_succ R 0).of_iso
      (I.isoRightDerivedObj (sectionsFunctor (twoChartLine R) ⊤) 1).symm
  have h' := (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp h
  exact (ShortComplex.ab_exact_iff _).mp h' z hz

/-- Every positive original right-derived degree vanishes. -/
theorem original_positive_map (R : CommRingCat.{u}) (n : ℕ) (A : AddCommGrpCat.{u})
    (f : ((sectionsFunctor (twoChartLine R) ⊤).rightDerived (n + 1)).obj
      (tautologicalQuotientLine R) ⟶ A) : f = 0 :=
  (isZero_rightDerived_tautologicalQuotientLine_succ R n).eq_of_src _ _

/-- The original first cohomology vanishing includes nonreduced rings. -/
theorem nonreduced_base :
    IsZero (((sectionsFunctor (twoChartLine (.of (ZMod 4))) ⊤).rightDerived 1).obj
      (tautologicalQuotientLine (.of (ZMod 4)))) :=
  isZero_rightDerived_tautologicalQuotientLine_succ (.of (ZMod 4)) 0

/-- The zero ring is retained in every positive degree. -/
theorem zero_base (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine (.of (ZMod 1))) ⊤).rightDerived (n + 1)).obj
      (tautologicalQuotientLine (.of (ZMod 1)))) :=
  isZero_rightDerived_tautologicalQuotientLine_succ (.of (ZMod 1)) n

end QuillenTest.ProjectiveLineTautologicalQuotientCohomology
