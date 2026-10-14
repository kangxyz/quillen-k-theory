/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementStalkTotalMatrix

/-! # Joint reflection of the original total augmentation by actual module stalks -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- The original module stalks jointly detect a zero original module sheaf. -/
theorem godement_isZero_of_moduleStalks {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x, IsZero ((moduleStalk X x).obj M)) : IsZero M := by
  apply (isZero_iff_stalks _).mpr
  intro x
  exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero (h x)).of_iso
    ((moduleStalkForgetIso X x).app M).symm

/-- Exact original module stalks jointly reflect isomorphisms of original module sheaves. -/
theorem godement_isIso_of_moduleStalks {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x, IsIso ((moduleStalk X x).map f)) : IsIso f := by
  have hker : IsZero (kernel f) := by
    apply godement_isZero_of_moduleStalks
    intro x
    have := h x
    exact (isZero_kernel_of_mono ((moduleStalk X x).map f)).of_iso
      (PreservesKernel.iso (moduleStalk X x) f)
  have hcoker : IsZero (cokernel f) := by
    apply godement_isZero_of_moduleStalks
    intro x
    have := h x
    exact (isZero_cokernel_of_epi ((moduleStalk X x).map f)).of_iso
      (PreservesCokernel.iso (moduleStalk X x) f)
  have : Mono f := Preadditive.mono_of_isZero_kernel f hker
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hcoker
  exact isIso_of_mono_of_epi f

/-- Actual stalk quasi-isomorphisms jointly imply a quasi-isomorphism of original complexes. -/
theorem godement_quasiIso_of_moduleStalks {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (h : ∀ x, QuasiIso (((moduleStalk X x).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    apply godement_isIso_of_moduleStalks
    intro x
    let F := moduleStalk X x
    let t := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℤ) n).map f
    have hq : ShortComplex.QuasiIso (F.mapShortComplex.map t) :=
      (quasiIsoAt_iff _ n).mp ((h x).quasiIsoAt n)
    have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map t)) :=
      (ShortComplex.quasiIso_iff _).mp hq
    have he : F.map (HomologicalComplex.homologyMap f n) =
        ((K.sc n).mapHomologyIso F).inv ≫
          ShortComplex.homologyMap (F.mapShortComplex.map t) ≫
            ((L.sc n).mapHomologyIso F).hom := by
      symm
      change ((K.sc n).mapHomologyIso F).inv ≫
          ShortComplex.homologyMap (F.mapShortComplex.map t) ≫ ((L.sc n).mapHomologyIso F).hom =
            F.map (ShortComplex.homologyMap t)
      rw [ShortComplex.mapHomologyIso_hom_naturality t F]
      simp only [Iso.inv_hom_id_assoc]
    rw [he]
    infer_instance

end Quillen.SchemeSheaf
