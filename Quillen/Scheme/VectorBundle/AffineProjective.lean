import Quillen.Scheme.Regular.AffineProjective
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-! # Finite projective sections of affine vector bundles over arbitrary rings

Finite local bases descend finite presentation of the module of global
sections along a principal-open cover. The existing local-freeness criterion
then proves projectivity, without a noetherianity assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped ModuleCat.Algebra

namespace Quillen.SchemeSheaf

/-- The actual global sections of an affine vector bundle are finitely
presented over the arbitrary base ring. -/
theorem finitePresentation_globalSections_of_finiteLocallyFree (R : CommRingCat.{u})
    (M : (Spec R).Modules) [hM : IsFiniteLocallyFree (Spec R) M] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  classical
  let N := moduleSpecΓFunctor.obj M
  have : Module.Finite R N := finite_globalSections_of_finiteLocallyFree R M
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let T : Set R := {r | Module.Free (Localization.Away r)
    (CoherentScheme.restrictionGlobalSections R r N)}
  have hT : Ideal.span T = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro x hx
    obtain ⟨q, hq, hf⟩ := hM.exists_localBasis
    obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := q.coversTop ⊤ x (by simp)
    have hxi : x ∈ q.X i := (leOfHom g) hxV
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxi (q.X i).2
    have hr : r ∈ T := by
      have := hq.isIso i
      have := free_restrictPrincipal_of_overBasis R M r (q.X i) hrU (q.generators i)
      let e := moduleSpecΓFunctor.mapIso
        ((Scheme.Modules.restrictFunctor (CoherentScheme.principalOpen R r)).mapIso
          (asIso M.fromTildeΓ))
      exact Module.Free.of_equiv e.toLinearEquiv.symm
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr ⟨hr, hxr⟩⟩
  apply Module.FinitePresentation.of_localizationSpan' T hT
    (Rₚ := fun r ↦ Localization.Away r.val)
    (fun r ↦ CoherentScheme.toRestrictionGlobalSections R r.val N)
  intro r
  have : Module.Free (Localization.Away r.val)
      (CoherentScheme.restrictionGlobalSections R r.val N) := r.property
  have : Module.Finite (Localization.Away r.val)
      (CoherentScheme.restrictionGlobalSections R r.val N) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers r.val)
      (CoherentScheme.toRestrictionGlobalSections R r.val N)
  exact Module.finitePresentation_of_projective _ _

/-- Affine vector bundles have genuinely projective modules of global sections,
without a noetherianity hypothesis. This is not global projectivity as sheaves. -/
theorem projective_globalSections_of_finiteLocallyFree (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    Module.Projective R (moduleSpecΓFunctor.obj M) := by
  have : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) :=
    finitePresentation_globalSections_of_finiteLocallyFree R M
  have : IsFiniteLocallyFree (Spec R) (tilde (moduleSpecΓFunctor.obj M)) :=
    finiteLocallyFree_of_iso (asIso M.fromTildeΓ).symm
  exact projective_of_finiteLocallyFree_tilde R (moduleSpecΓFunctor.obj M)

end Quillen.SchemeSheaf
