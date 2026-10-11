/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineExactness
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.UnitPushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Actual affine principal-kernel cokernel presentations

A surjective ring map with principal kernel gives the cokernel universal property of its
original structure-module map. The proofs retain the original ΓSpec naturality equations
and sheaf maps over arbitrary commutative rings, without noetherianity assumptions.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.SchemeSheaf
/-- The literal affine section map sends the section of a ring-kernel element to zero. -/
theorem spec_scalar_image_zero {R S : CommRingCat.{u}} (φ : R ⟶ S) (s : R)
    (hs : φ.hom s = 0) :
    (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom s) = 0 := by
  have h := congrArg (fun f => CommRingCat.Hom.hom f s) (Scheme.ΓSpecIso_inv_naturality φ)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, hs, map_zero] using h.symm
/-- A principal ring kernel gives the actual principal kernel on global structure sections. -/
theorem spec_scalar_kernel {R S : CommRingCat.{u}} (φ : R ⟶ S) (s : R)
    (hker : RingHom.ker φ.hom = Ideal.span {s}) :
    ∀ x : Γ(Spec R, ⊤), (Spec.map φ).appTop.hom x = 0 →
      ∃ y, y * (Scheme.ΓSpecIso R).inv.hom s = x := by
  intro x hx
  have hn := congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso_naturality φ)
  have hm : (Scheme.ΓSpecIso R).hom.hom x ∈ RingHom.ker φ.hom := by
    change φ.hom ((Scheme.ΓSpecIso R).hom.hom x) = 0
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, hx, map_zero] using hn.symm
  rw [hker, Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  refine ⟨(Scheme.ΓSpecIso R).inv.hom y, ?_⟩
  have he := congrArg (Scheme.ΓSpecIso R).inv.hom hy
  simpa using he
/-- Surjectivity of the original ring map gives surjectivity of its actual global section map. -/
theorem spec_appTop_surjective {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Surjective φ.hom) : Function.Surjective (Spec.map φ).appTop.hom := by
  intro x
  obtain ⟨y, hy⟩ := hφ ((Scheme.ΓSpecIso S).hom.hom x)
  refine ⟨(Scheme.ΓSpecIso R).inv.hom y, ?_⟩
  have hn := congrArg (fun f => CommRingCat.Hom.hom f y) (Scheme.ΓSpecIso_inv_naturality φ)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, hy,
    CommRingCat.inv_hom_apply] using hn.symm
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Pointwise additivity of the actual affine global-section functor. -/
local instance (R : CommRingCat.{u}) : (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intros; rfl
/-- The scalar and original structure-module map form the actual affine short complex. -/
def affineUnitScalarSequence {R S : CommRingCat.{u}} (φ : R ⟶ S) (s : Γ(Spec R, ⊤))
    (hs : (Spec.map φ).appTop.hom s = 0) : ShortComplex (Spec R).Modules :=
  ShortComplex.mk (unitMul (Spec R) s)
    (SheafOfModules.unitToPushforwardObjUnit (Spec.map φ).toRingCatSheafHom)
    (unitMul_unitToPushforward_zero (Spec.map φ) s hs)
/-- The actual principal-kernel condition proves exactness of the original affine sheaf maps. -/
theorem affineUnitScalarSequence_exact {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (s : Γ(Spec R, ⊤)) (hs : (Spec.map φ).appTop.hom s = 0)
    (hex : ∀ x : Γ(Spec R, ⊤), (Spec.map φ).appTop.hom x = 0 →
      ∃ y, y * s = x) : (affineUnitScalarSequence φ s hs).Exact := by
  have hunit (A : CommRingCat.{u}) :
      (SheafOfModules.unit (Spec A).ringCatSheaf).IsQuasicoherent := by
    let e : SheafOfModules.free (R := (Spec A).ringCatSheaf) (ULift.{u} Unit) ≅
        SheafOfModules.unit (Spec A).ringCatSheaf := coproductUniqueIso _
    exact (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso e (by infer_instance)
  have := hunit R
  have := hunit S
  have : IsIso (Scheme.Modules.fromTildeΓ (SheafOfModules.unit (Spec S).ringCatSheaf)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit (Spec S).ringCatSheaf)).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ _
  have hQC : ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit (Spec S).ringCatSheaf)).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  unfold affineUnitScalarSequence
  apply @exact_of_exact_globalSections R _ (hunit R) (hunit R) hQC
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change (Spec.map φ).appTop.hom x = 0 at hx
  obtain ⟨y, hy⟩ := hex x hx
  exact ⟨y, hy⟩
/-- Surjectivity of the original affine section map makes the original unit arrow epic. -/
theorem epi_unitToPushforward_of_surjective_appTop {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Surjective (Spec.map φ).appTop.hom) :
    Epi (SheafOfModules.unitToPushforwardObjUnit (Spec.map φ).toRingCatSheafHom) := by
  have hunit (A : CommRingCat.{u}) :
      (SheafOfModules.unit (Spec A).ringCatSheaf).IsQuasicoherent := by
    let e : SheafOfModules.free (R := (Spec A).ringCatSheaf) (ULift.{u} Unit) ≅
        SheafOfModules.unit (Spec A).ringCatSheaf := coproductUniqueIso _
    exact (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso e (by infer_instance)
  have := hunit R
  have := hunit S
  have : IsIso (Scheme.Modules.fromTildeΓ (SheafOfModules.unit (Spec S).ringCatSheaf)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit (Spec S).ringCatSheaf)).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ _
  have hQC : ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit (Spec S).ringCatSheaf)).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  have hΓ : Epi (moduleSpecΓFunctor.map
      (SheafOfModules.unitToPushforwardObjUnit (Spec.map φ).toRingCatSheafHom)) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact hφ
  exact @epi_of_epi_globalSections R _ _ (hunit R) hQC _ hΓ
/-- The actual principal-kernel sequence exhibits the original unit arrow as a cokernel. -/
def affineUnitScalarSequenceCokernel {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (s : Γ(Spec R, ⊤)) (hs : (Spec.map φ).appTop.hom s = 0)
    (hex : ∀ x : Γ(Spec R, ⊤), (Spec.map φ).appTop.hom x = 0 →
      ∃ y, y * s = x) (hφ : Function.Surjective (Spec.map φ).appTop.hom) :
    IsColimit (CokernelCofork.ofπ (affineUnitScalarSequence φ s hs).g
      (affineUnitScalarSequence φ s hs).zero) := by
  have : Epi (affineUnitScalarSequence φ s hs).g :=
    epi_unitToPushforward_of_surjective_appTop φ hφ
  exact (affineUnitScalarSequence_exact φ s hs hex).gIsCokernel
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- The literal scalar/structure-map short complex of an original ring-map kernel element. -/
def affinePrincipalSequence {R S : CommRingCat.{u}} (φ : R ⟶ S) (s : R)
    (hs : φ.hom s = 0) : ShortComplex (Spec R).Modules :=
  affineUnitScalarSequence φ ((Scheme.ΓSpecIso R).inv.hom s) (spec_scalar_image_zero φ s hs)
/-- The actual original affine structure map is the cokernel of a principal kernel generator. -/
def affinePrincipalSequenceCokernel {R S : CommRingCat.{u}} (φ : R ⟶ S) (s : R)
    (hs : φ.hom s = 0) (hker : RingHom.ker φ.hom = Ideal.span {s})
    (hφ : Function.Surjective φ.hom) :
    IsColimit (CokernelCofork.ofπ (affinePrincipalSequence φ s hs).g
      (affinePrincipalSequence φ s hs).zero) :=
  affineUnitScalarSequenceCokernel φ ((Scheme.ΓSpecIso R).inv.hom s)
    (spec_scalar_image_zero φ s hs) (spec_scalar_kernel φ s hker)
    (spec_appTop_surjective φ hφ)
end Quillen.SchemeSheaf
