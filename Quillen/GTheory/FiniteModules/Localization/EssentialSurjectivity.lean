/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.FiniteLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! Every finite module over a localization descends to a finite module over the
original ring, by taking the original-ring span of finitely many generators. -/
@[expose] public section

open ModuleCat.FiniteLocalization



noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.FiniteModuleLocalization
variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Finite modules over a localized ring are localizations of finite modules.
No noetherian assumption is needed for this essential-surjectivity statement. -/
instance functor_essSurj : (functor S).EssSurj where
  mem_essImage N := by
    let : Module R N := Module.compHom N (algebraMap R (Localization S))
    let : IsScalarTower R (Localization S) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let : IsLocalizedModule S (LinearMap.id : N →ₗ[R] N) :=
      isLocalizedModule_id S N (Localization S)
    obtain ⟨s, hs⟩ := (inferInstance : Module.Finite (Localization S) N).1
    let M : Submodule R N := Submodule.span R (s : Set N)
    let : Module.Finite R M := Module.Finite.of_fg (Submodule.fg_span s.finite_toSet)
    have hM : M.localized' (Localization S) S (LinearMap.id : N →ₗ[R] N) = ⊤ := by
      rw [Submodule.localized'_eq_span]
      simpa only [LinearMap.id_coe, Set.image_id, M, Submodule.span_span_of_tower] using hs
    let e : (M.localized' (Localization S) S (LinearMap.id : N →ₗ[R] N)) ≃ₗ[Localization S] N :=
      (LinearEquiv.ofEq _ _ hM).trans Submodule.topEquiv
    have hloc : IsLocalizedModule S ((ModuleCat.of.{u} R M).localizedModuleMkLinearMap S) :=
      ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of.{u} R M) S
    let e' : (ModuleCat.of.{u} R M).localizedModule S ≃ₗ[R]
        M.localized' (Localization S) S (LinearMap.id : N →ₗ[R] N) :=
      IsLocalizedModule.linearEquiv S
      ((ModuleCat.of.{u} R M).localizedModuleMkLinearMap S)
      (M.toLocalized' (Localization S) S (LinearMap.id : N →ₗ[R] N))
    refine ⟨FGModuleCat.of R M, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    exact ((e'.extendScalarsOfIsLocalization S (Localization S)).trans e).toModuleIso

end Quillen.FiniteModuleLocalization
