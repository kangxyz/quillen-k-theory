/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.ModuleComplex.PrincipalDenominators

/-!
# Actual descent of principal-localized complex differentials

Finite differential denominators are cleared and their squares are killed by
an actual uniform scalar power over the original ring. Integer powers of the
resulting localized unit rescale the terms, producing a genuine chain
isomorphism with the original localized complex. The term models must be
finitely presented and finitely supported; no descent of arbitrary projective
modules is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Quillen.ModuleComplex.PrincipalLocalization
variable {R : Type u} [CommRing R]

/-- Actual finitely supported localized differentials descend after one common
power, and their square vanishes before localization after genuine torsion killing. -/
theorem exists_differential_descent (r : R) (M : ℤ → ModuleCat.{u} R)
    (s : Finset ℤ) (hz : ∀ i ∉ s, IsZero (M i))
    (hfp : ∀ i, Module.FinitePresentation R (M i))
    (d : ∀ i, (M i).localizedModule (Submonoid.powers r) ⟶
      (M (i + 1)).localizedModule (Submonoid.powers r))
    (hd : ∀ i, d i ≫ d (i + 1) = 0) :
    ∃ (n : ℕ) (δ : ∀ i, M i ⟶ M (i + 1)), (∀ i, δ i ≫ δ (i + 1) = 0) ∧
      ∀ i, (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (δ i) =
        algebraMap R (Localization (Submonoid.powers r)) (r^n) • d i := by
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  obtain ⟨n, δ₀, hδ₀⟩ := exists_family_denominator r M (fun i => M (i + 1)) s hz hfp d
  have hfin (i : ℤ) : Module.Finite R (M i) := by let := hfp i; infer_instance
  have heq (i : ℤ) : F.map (δ₀ i ≫ δ₀ (i + 1)) = F.map (0 : M i ⟶ M (i+1+1)) := by
    rw [Functor.map_comp, hδ₀, hδ₀, Linear.smul_comp, Linear.comp_smul, hd]
    simp
  obtain ⟨m, hm⟩ := exists_family_power_eq r M (fun i => M (i+1+1)) s hz hfin
    (fun i => δ₀ i ≫ δ₀ (i + 1)) (fun _ => 0) heq
  refine ⟨m+n, fun i => r^m • δ₀ i, ?_, ?_⟩
  · intro i
    rw [Linear.smul_comp, Linear.comp_smul, hm]
    simp
  · intro i
    rw [localization_map_smul, hδ₀, smul_smul, ← map_mul, ← pow_add]

/-- Multiplication by an actual unit gives the original scalar automorphism of a module. -/
def unitScalarIso {S : Type u} [CommRing S] (a : Sˣ) (M : ModuleCat.{u} S) : M ≅ M where
  hom := (a : S) • 𝟙 M
  inv := ((a⁻¹ : Sˣ) : S) • 𝟙 M
  hom_inv_id := by simp [Linear.comp_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_smul, smul_smul]

/-- The rescaling needed to undo a common unit factor in every differential. -/
theorem unit_rescaling_identity {S : Type u} [CommRing S] (a : Sˣ) (i : ℤ) :
    (a : S) * ((a ^ (-(i + 1))) : Sˣ) = ((a ^ (-i)) : Sˣ) := by
  change ((a * a ^ (-(i + 1)) : Sˣ) : S) = ((a ^ (-i) : Sˣ) : S)
  congr 1
  rw [← zpow_one_add]
  congr 1
  omega

/-- A bounded finite-presentation family whose actual localized terms are the
terms of a complex supports a genuine descended differential and a chain isomorphism. -/
theorem exists_complex_descent_with_terms (r : R) (M : ℤ → ModuleCat.{u} R)
    (s : Finset ℤ) (hz : ∀ i ∉ s, IsZero (M i))
    (hfp : ∀ i, Module.FinitePresentation R (M i))
    (K : CochainComplex (ModuleCat.{u} (Localization (Submonoid.powers r))) ℤ)
    (e : ∀ i, (M i).localizedModule (Submonoid.powers r) ≅ K.X i) :
    ∃ (δ : ∀ i, M i ⟶ M (i + 1)) (hδ : ∀ i, δ i ≫ δ (i + 1) = 0),
      Nonempty ((localize r (.up ℤ)).obj (CochainComplex.of M δ hδ) ≅ K) := by
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  let d (i : ℤ) := (e i).hom ≫ K.d i (i + 1) ≫ (e (i + 1)).inv
  have hd (i : ℤ) : d i ≫ d (i + 1) = 0 := by
    dsimp [d]
    simp [Category.assoc]
  obtain ⟨n, δ, hsq, hδ⟩ := exists_differential_descent r M s hz hfp d hd
  obtain ⟨a, ha⟩ := IsLocalization.map_units (Localization (Submonoid.powers r))
    (⟨r^n, n, rfl⟩ : Submonoid.powers r)
  change (a : Localization (Submonoid.powers r)) = algebraMap R (Localization (Submonoid.powers r))
    (r^n) at ha
  have hδ' (i : ℤ) : F.map (δ i) = (a : Localization (Submonoid.powers r)) • d i := by
    simpa only [ha] using hδ i
  refine ⟨δ, hsq, ⟨HomologicalComplex.Hom.isoOfComponents
    (fun i => unitScalarIso (a ^ (-i)) (F.obj (M i)) ≪≫ e i) ?_⟩⟩
  intro i j hij
  obtain rfl : j = i+1 := hij.symm
  change ((unitScalarIso (a ^ (-i)) (F.obj (M i))).hom ≫ (e i).hom) ≫ K.d i (i + 1) =
    F.map ((CochainComplex.of M δ hsq).d i (i + 1)) ≫
      ((unitScalarIso (a ^ (-(i + 1))) (F.obj (M (i + 1)))).hom ≫ (e (i + 1)).hom)
  dsimp only [CochainComplex.of]
  rw [CochainComplex.of_d, hδ']
  dsimp [unitScalarIso, d]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.inv_hom_id, smul_smul]
  rw [mul_comm, unit_rescaling_identity]

end Quillen.ModuleComplex.PrincipalLocalization
