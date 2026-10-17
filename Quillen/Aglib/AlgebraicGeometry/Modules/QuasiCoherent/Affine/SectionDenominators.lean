/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Quillen.Aglib.AlgebraicGeometry.Modules.Restriction.UnitSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators

/-!
# Actual affine section denominators

A quasicoherent section on the stated principal open admits an actual scalar denominator. The
original unit-sheaf map and geometric open-image equation are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- Every section on a genuine principal affine open has a numerator after
multiplication by a power of the original coordinate-ring element. -/
theorem affine_section_denominator (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) (s : Γ(M, PrimeSpectrum.basicOpen r)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op t = r ^ n • s := by
  have h : IsLocalizedModule.Away r
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r
  obtain ⟨n, t, ht⟩ := h.surj _ _ s
  exact ⟨n, t, ht.symm⟩

/-- The actual affine coordinate action agrees with the action after restricting
along an arbitrary open immersion, through the original section comparison. -/
theorem affine_scalar_restrict_section {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) [IsOpenImmersion j] (M : (Spec R).Modules)
    (r : R) (s : Γ(M.restrict j, ⊤)) :
    (M.restrictAppIso j ⊤).hom (j.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) • s) =
      r • (M.restrictAppIso j ⊤).hom s := by
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.smul_Spec_def]
  have he : j.appTop ≫ (j.appIso ⊤).inv =
      (Spec R).presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using
      j.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)
  exact congrArg (fun c => c • (M.restrictAppIso j ⊤).hom s)
    (congrArg (fun f => CommRingCat.Hom.hom f ((Scheme.ΓSpecIso R).inv.hom r)) he)

/-- An actual unit-sheaf map on a principal affine open extends after a power
of the original coordinate. The equation retains the original restriction
unit, scalar map, and local morphism. -/
theorem exists_unit_map_denominator {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) [IsOpenImmersion j] (M : (Spec R).Modules) [M.IsQuasicoherent]
    (r : R) (himage : j ''ᵁ ⊤ = PrimeSpectrum.basicOpen r)
    (f : (SheafOfModules.unit X.ringCatSheaf) ⟶ M.restrict j) :
    ∃ (n : ℕ) (g : (SheafOfModules.unit (Spec R).ringCatSheaf) ⟶ M),
      (Scheme.Modules.restrictUnitIso j).inv ≫ (Scheme.Modules.restrictFunctor j).map g =
        unitMul X (j.appTop.hom ((Scheme.ΓSpecIso R).inv.hom (r ^ n))) ≫ f := by
  let N := (modulesSpecToSheaf.obj M).obj
  let e : N.obj (op (j ''ᵁ ⊤)) ≅ N.obj (op (PrimeSpectrum.basicOpen r)) :=
    (N.mapIso (eqToIso himage).op).symm
  let x : Γ(M.restrict j, ⊤) := Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤))
  obtain ⟨n, t, ht⟩ := affine_section_denominator R M r
    (e.hom ((M.restrictAppIso j ⊤).hom x))
  have he : N.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫ e.hom =
      N.map (PrimeSpectrum.basicOpen r).leTop.op := by
    dsimp only [e, Iso.symm_hom, Functor.mapIso_inv]
    rw [← N.map_comp]
    congr 1
  have hsec : restrictedTopSection j M t =
      j.appTop.hom ((Scheme.ΓSpecIso R).inv.hom (r ^ n)) • x := by
    apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso j ⊤).hom).1
    rw [affine_scalar_restrict_section]
    apply e.toLinearEquiv.injective
    change e.hom.hom (M.presheaf.map
        (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op t) =
      e.hom.hom (r ^ n • (M.restrictAppIso j ⊤).hom x)
    rw [_root_.map_smul]
    have he' := congrArg (fun q => (q : N.obj (op ⊤) ⟶
      N.obj (op (PrimeSpectrum.basicOpen r))) t) he
    change e.hom.hom (M.presheaf.map
      (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op t) =
        M.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op t at he'
    rw [he']
    exact ht
  refine ⟨n, unitMapOfTopSection M t, ?_⟩
  rw [unitMapOfTopSection_restrict, hsec, unitMapOfTopSection_smul]
  change _ ≫ unitMapOfTopSection (M.restrict j)
      (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤))) = _
  rw [unitMapOfTopSection_of_map]


end Quillen.PerfectComplexes.ProjectiveLine
end
end
