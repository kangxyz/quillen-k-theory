/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.StructureSheafDirectImage
public import Mathlib.Data.ZMod.Basic

/-! # Literal relative structure-sheaf maps and original-resolution consumers -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.SchemeSheaf.TwoOpen Quillen.Scheme.ProjectiveLine
universe u
namespace Quillen.Tests.ProjectiveLineStructureSheafDirectImage

/-- The actual direct-image isomorphism has the original geometric ring map on every open. -/
theorem original_unit_sections (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    Scheme.Modules.Hom.app (projectionUnitIso R).hom U =
      AddCommGrpCat.ofHom ((projection R).app U).hom.toAddMonoidHom := rfl

/-- The inverse direct-image comparison cancels precisely the original unit map. -/
theorem original_unit_inverse (R : CommRingCat.{u}) :
    projectionUnitMap R ≫ (projectionUnitIso R).inv = 𝟙 _ :=
  (projectionUnitIso R).hom_inv_id

/-- A resolution cocycle on a principal inverse image has an original local section lift. -/
theorem original_principal_cocycle_boundary (R : CommRingCat.{u}) (r : R)
    (I : InjectiveResolution (SheafOfModules.unit (twoChartLine R).ringCatSheaf))
    (z : Γ(I.cocomplex.X 1, (projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r))
    (hz : Scheme.Modules.Hom.app (I.cocomplex.d 1 2)
      ((projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r) z = 0) :
    ∃ y : Γ(I.cocomplex.X 0, (projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r),
      Scheme.Modules.Hom.app (I.cocomplex.d 0 1)
        ((projection R) ⁻¹ᵁ PrimeSpectrum.basicOpen r) y = z := by
  have h := projection_unit_resolution_on_open_exact (R := R)
    (CommRingCat.ofHom (algebraMap R (Localization.Away r))) I 0
  rw [Scheme.Hom.opensRange_localizationAway (R := R)] at h
  have h' := (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp h
  exact (ShortComplex.ab_exact_iff _).mp h' z hz

/-- Positive derived module-sheaf arrows out of the actual direct image vanish. -/
theorem original_positive_derived_map (R : CommRingCat.{u}) (n : ℕ)
    (N : (Spec R).Modules)
    (f : ((Scheme.Modules.pushforward (projection R)).rightDerived (n + 1)).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf) ⟶ N) : f = 0 :=
  (isZero_rightDerived_projection_unit_succ R n).eq_of_src _ _

/-- The literal direct-image unit is invertible over a nonreduced ring. -/
theorem nonreduced_unit : IsIso (projectionUnitMap (.of (ZMod 4))) := inferInstance

/-- All positive relative degrees include the zero-ring case. -/
theorem zero_ring_positive (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward (projection (.of (ZMod 1)))).rightDerived (n + 1)).obj
      (SheafOfModules.unit (twoChartLine (.of (ZMod 1))).ringCatSheaf)) :=
  isZero_rightDerived_projection_unit_succ _ n

end Quillen.Tests.ProjectiveLineStructureSheafDirectImage
