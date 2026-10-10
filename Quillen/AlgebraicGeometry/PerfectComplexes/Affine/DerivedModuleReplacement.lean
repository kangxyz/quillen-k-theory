/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StrictModuleModel
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Quillen.Algebra.Homology.KProjectiveRepresentatives

/-!
# Principal-open derived replacement for bounded finite-projective modules

The denominator construction is promoted to the actual module derived
category using the proved K-projectivity of bounded projective complexes.
This does not assert the separate affine comparison with the derived
category of all sheaves or that every locally perfect sheaf complex is
already globally strict perfect.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization

/-- Bounded finite-projective module complexes are genuinely K-projective. -/
theorem isKProjective_of_moduleStrictPerfect (R : CommRingCat.{u}) {K : ModuleComplex R}
    (hK : moduleStrictPerfect R K) : K.IsKProjective := by
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  have : K.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hb i (Or.inr hi)
  have (i : ℤ) : CategoryTheory.Projective (K.X i) := by
    let := (hp i).2
    infer_instance
  exact CochainComplex.isKProjective_of_projective K b


attribute [local instance] HasDerivedCategory.standard

/-- Principal-open derived morphism replacement in the actual module
model. A uniform scalar denominator is invertible as a chain map after
localization, and the equation preserves the original derived morphism. -/
theorem exists_principal_derived_module_fraction (R : CommRingCat.{u}) (r : R)
    {K L : ModuleComplex R} (hK : moduleStrictPerfect R K)
    (α : DerivedCategory.Q.obj ((localize r (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj ((localize r (ComplexShape.up ℤ)).obj L)) :
    ∃ (n : ℕ) (g : K ⟶ L),
      IsIso ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K)) ∧
      DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K)) ≫ α =
        DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map g) := by
  have : CochainComplex.IsKProjective ((localize r (ComplexShape.up ℤ)).obj K) :=
    isKProjective_of_moduleStrictPerfect _ (moduleStrictPerfect_localize R r hK)
  obtain ⟨f, rfl⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKProjective α
  obtain ⟨n, g, hn, hg⟩ := exists_moduleStrictPerfect_fraction R r hK f
  refine ⟨n, g, hn, ?_⟩
  rw [← DerivedCategory.Q.map_comp, hg]

/-- Derived equality after principal localization descends after one
source denominator. It is proved using the actual localized homotopy,
not an assumed faithfulness or replacement property. -/
theorem exists_principal_derived_module_equality (R : CommRingCat.{u}) (r : R)
    {K L : ModuleComplex R} (hK : moduleStrictPerfect R K) (f g : K ⟶ L)
    (h : DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map ((localize r (ComplexShape.up ℤ)).map g)) :
    ∃ n : ℕ, IsIso ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K)) ∧
      DerivedCategory.Q.map ((r ^ n • 𝟙 K) ≫ f) =
        DerivedCategory.Q.map ((r ^ n • 𝟙 K) ≫ g) := by
  have : CochainComplex.IsKProjective ((localize r (ComplexShape.up ℤ)).obj K) :=
    isKProjective_of_moduleStrictPerfect _ (moduleStrictPerfect_localize R r hK)
  let H := Quillen.CochainComplex.homotopyOfDerivedEqOfIsKProjective
    ((localize r (ComplexShape.up ℤ)).map f) ((localize r (ComplexShape.up ℤ)).map g) h
  obtain ⟨⟨s, hs⟩, hfp⟩ := moduleStrictPerfect_denominator_inputs R hK
  obtain ⟨n, H', _⟩ := exists_homotopy_denominator r s hs hfp f g H
  refine ⟨n, localize_power_id_isIso r K n, ?_⟩
  simpa only [Linear.smul_comp, Category.id_comp] using
    DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R) H'

end Quillen.PerfectComplexes.Affine
