/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalSections

/-!
# Vanishing of actual tautological-line cohomology

The bijective original signed chart restriction map gives zero global sections
and zero first derived global sections. The proved higher two-affine-cover theorem
then gives vanishing in every degree, over an arbitrary commutative base ring.
This concerns the actual tautological subline on `twoChartLine`; no Proj comparison
or projective-bundle K-theory formula is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf Quillen.SchemeSheaf.TwoOpen
variable (R : CommRingCat.{u})

/-- First actual derived global sections of the tautological line vanish. -/
theorem isZero_rightDerived_tautologicalLine_one :
    IsZero (((sectionsFunctor (twoChartLine R) ⊤).rightDerived 1).obj (tautologicalLine R)) :=
  twoAffine_isZero_rightDerived_one_of_difference_surjective (tautologicalLine R)
    (plusChart R) (minusChart R) (chart_ranges_cover R) (tautological_difference_surjective R)

/-- All positive actual derived global sections of the tautological line vanish. -/
theorem isZero_rightDerived_tautologicalLine_succ (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine R) ⊤).rightDerived (n + 1)).obj
      (tautologicalLine R)) := by
  cases n with
  | zero => exact isZero_rightDerived_tautologicalLine_one R
  | succ n => exact isZero_rightDerived_globalSections_add_two R (tautologicalLine R) n

/-- The original global section group of the tautological line is zero. -/
theorem isZero_globalSections_tautologicalLine : IsZero Γ(tautologicalLine R, ⊤) := by
  rw [IsZero.iff_id_eq_zero]
  ext a
  change a = 0
  apply augmentation_injective (tautologicalLine R)
    (plusChart R).opensRange (minusChart R).opensRange (chart_ranges_cover R)
  apply tautological_difference_injective R
  have h := difference_augmentation (tautologicalLine R)
    (plusChart R).opensRange (minusChart R).opensRange
  have ha := DFunLike.congr_fun h a
  have hb := DFunLike.congr_fun h 0
  exact ha.trans hb.symm

/-- All actual derived global sections of the tautological line vanish, including degree zero. -/
theorem isZero_rightDerived_tautologicalLine (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine R) ⊤).rightDerived n).obj
      (tautologicalLine R)) := by
  cases n with
  | zero =>
    exact (isZero_globalSections_tautologicalLine R).of_iso
      ((sectionsFunctor (twoChartLine R) ⊤).rightDerivedZeroIsoSelf.app (tautologicalLine R))
  | succ n => exact isZero_rightDerived_tautologicalLine_succ R n

end Quillen.Scheme.ProjectiveLine
