/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.ModuleComplex.PrincipalDenominators
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Actual finite-projective locality on principal covers

Local splittings of a map onto a finitely presented module descend after
powers by the proved module-Hom denominator and torsion-killing theorems.
The power-span criterion patches them to a genuine original-ring section.
Together with actual finite-presentation descent this proves finite-projective
locality for any generating family of principal localizations. The source of
the patched epimorphism is unrestricted, and no noetherianity is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.ModuleComplex.PrincipalLocalization
variable {R : Type u} [CommRing R]

/-- Actual principal-local sections of a map onto a finitely presented module
patch to an original global section. The source module is unrestricted. -/
theorem exists_section_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    {N M : ModuleCat.{u} R} [Module.FinitePresentation R M] (f : N ⟶ M)
    (hloc : ∀ r : s, ∃ g : M.localizedModule (Submonoid.powers r.val) ⟶
      N.localizedModule (Submonoid.powers r.val),
      g ≫ (ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)).map f = 𝟙 _) :
    ∃ g : M ⟶ N, g ≫ f = 𝟙 M := by
  let L : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] M) := LinearMap.llcomp R M N M f.hom
  have hid : (LinearMap.id : M →ₗ[R] M) ∈ LinearMap.range L := by
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs _
    intro r
    obtain ⟨g, hg⟩ := hloc r
    obtain ⟨n, a, ha⟩ := exists_module_denominator r.val M N g
    let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
    have heq : F.map (a ≫ f) = F.map (r.val ^ n • 𝟙 M) := by
      rw [F.map_comp, ha, Linear.smul_comp, hg, localization_map_smul, F.map_id]
      rfl
    obtain ⟨m, hm⟩ := exists_module_power_eq r.val M M (a ≫ f) (r.val ^ n • 𝟙 M) heq
    have hfinal : (r.val ^ m • a) ≫ f = r.val ^ (m+n) • 𝟙 M := by
      rw [Linear.smul_comp, hm, smul_smul, pow_add]
    refine ⟨m+n, ?_⟩
    exact ⟨(r.val ^ m • a).hom, ModuleCat.hom_ext_iff.mp hfinal⟩
  obtain ⟨g, hg⟩ := hid
  exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩

/-- Finite presentation and actual projectivity on a principal cover imply
projectivity over the original ring, via the proved patched section. -/
theorem projective_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (hproj : ∀ r : s, Module.Projective (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val))) : Module.Projective R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let N := ModuleCat.of R (Fin n → R)
  let fc : N ⟶ M := ModuleCat.ofHom f
  have : Epi fc := (ModuleCat.epi_iff_surjective fc).mpr hf
  obtain ⟨g, hg⟩ := exists_section_of_localizationSpan s hs fc (fun r => by
    let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
    let : Module.Projective (Localization (Submonoid.powers r.val)) (F.obj M) := hproj r
    have : Projective (F.obj M) := ModuleCat.projective_of_categoryTheory_projective (F.obj M)
    exact ⟨Projective.factorThru (𝟙 _) (F.map fc), Projective.factorThru_comp _ _⟩)
  exact Module.Projective.of_split g.hom fc.hom (ModuleCat.hom_ext_iff.mp hg)

/-- Actual finite-projective localized modules on any generating principal
cover imply genuine finite projectivity of the original module. -/
theorem finiteProjective_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (M : ModuleCat.{u} R)
    (hfin : ∀ r : s, Module.Finite (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val)))
    (hproj : ∀ r : s, Module.Projective (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val))) :
    Module.Finite R M ∧ Module.Projective R M := by
  have : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Rₚ := fun r => Localization.Away r.val)
      (fun r => M.localizedModuleMkLinearMap (Submonoid.powers r.val)) (fun r => by
      let := hfin r
      let := hproj r
      exact Module.finitePresentation_of_projective (Localization.Away r.val)
        (M.localizedModule (Submonoid.powers r.val)))
  exact ⟨inferInstance, projective_of_localizationSpan s hs M hproj⟩

end Quillen.ModuleComplex.PrincipalLocalization
