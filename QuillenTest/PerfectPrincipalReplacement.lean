/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedModuleReplacement
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalReplacement

/-! Semantic consumers: actual derived roofs, original homotopies, and
replacement for geometric chain maps from affine strict-perfect sheaf complexes to
arbitrary termwise quasicoherent sheaf complexes. -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard

namespace QuillenTest.AffinePrincipal

open Quillen

/-- The replacement recovers the exact input derived arrow as a roof. -/
theorem derived_roof_preserves_original (R : CommRingCat.{u}) (r : R)
    {K L : ModuleComplex R} (hK : moduleStrictPerfect R K)
    (α : DerivedCategory.Q.obj ((localize r (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj ((localize r (ComplexShape.up ℤ)).obj L)) :
    ∃ (n : ℕ) (g : K ⟶ L),
      ∃ _ : IsIso (DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K))),
      α = inv (DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K))) ≫
        DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map g) := by
  obtain ⟨n, g, hd, hg⟩ := exists_principal_derived_module_fraction R r hK α
  let := hd
  have hQ : IsIso (DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K))) :=
    (DerivedCategory.Q.mapIso (asIso ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙
      K)))).isIso_hom
  refine ⟨n, g, hQ, ?_⟩
  rw [← hg, IsIso.inv_hom_id_assoc]

/-- Clearing homotopies keeps their actual componentwise localization. -/
theorem original_homotopy_survives (R : Type u) [CommRing R] (r : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (s : Finset ℤ)
    (hz : ∀ i ∉ s, IsZero (K.X i))
    (hfp : ∀ i, Module.FinitePresentation R (K.X i)) (f g : K ⟶ L)
    (h : Homotopy ((localize r (ComplexShape.up ℤ)).map f)
      ((localize r (ComplexShape.up ℤ)).map g)) :
    ∃ (n : ℕ) (H : Homotopy (r ^ n • f) (r ^ n • g)),
      IsIso ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K)) ∧
      ∀ i j, (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (H.hom i j) =
        algebraMap R (Localization.Away r) (r ^ n) • h.hom i j := by
  obtain ⟨n, H, hH⟩ := exists_homotopy_denominator r s hz hfp f g h
  exact ⟨n, H, localize_power_id_isIso r K n, hH⟩

/-- The algebraic construction supplies actual source replacement for
geometric chain maps from affine strict-perfect to termwise quasicoherent complexes. -/
theorem geometric_strict_chain_replacement (R : CommRingCat.{u}) (r : R)
    {K L : Complex (Spec R)} (hK : strictPerfect (Spec R) K) (hL : ∀ i, (L.X i).IsQuasicoherent)
    (φ : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj K ⟶
      (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj L) :
    ∃ (s : K ⟶ K) (g : K ⟶ L),
      IsIso ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map s) ∧
      (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map s ≫ φ =
        (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map g := by
  exact Quillen.PerfectComplexes.Affine.geometric_strict_chain_replacement R r hK hL φ

end QuillenTest.AffinePrincipal
