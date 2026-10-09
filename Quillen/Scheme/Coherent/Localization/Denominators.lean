import Quillen.Scheme.Coherent.Restriction
import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-!
# Actual coherent restriction denominators

For an open immersion of locally noetherian schemes, restriction inverts
exactly the morphisms with coherent kernel and cokernel supported outside
the open. If two coherent sheaf maps agree on the open, their difference
has a coherent kernel whose inclusion is such a denominator. This proves
the equality/cancellation half of the geometric fraction calculus without
assuming coherent extension or a quotient equivalence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual support-Serre denominators are precisely the maps that become
isomorphisms under geometric coherent restriction. -/
theorem coherentSupportedAway_isoModSerre_iff {M N : Coherent X} (f : M ⟶ N) :
    (coherentSupportedAway j).isoModSerre f ↔ IsIso ((coherentRestriction j).map f) := by
  have h : (coherentSupportedAway j).isoModSerre f ↔
      (coherentRestriction j).kernel.isoModSerre f := by
    change (coherentSupportedAway j (kernel f) ∧ coherentSupportedAway j (cokernel f)) ↔ _
    rw [← coherentRestriction_kernel_eq_support j]
    rfl
  rw [h, Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  rfl

/-- Actual restriction inverts the supported coherent denominators. -/
theorem coherentRestriction_inverts_support :
    (coherentSupportedAway j).isoModSerre.IsInvertedBy (coherentRestriction j) := by
  intro M N f hf
  exact (coherentSupportedAway_isoModSerre_iff j f).mp hf

/-- A map vanishing after restriction has a genuine coherent kernel
subsheaf which equals its source over the open. -/
theorem coherent_kernel_denominator {M N : Coherent X} (f : M ⟶ N)
    (hf : (coherentRestriction j).map f = 0) :
    (coherentSupportedAway j).isoModSerre (kernel.ι f) := by
  rw [coherentSupportedAway_isoModSerre_iff]
  exact KernelFork.IsLimit.isIso_ι _
    (KernelFork.mapIsLimit _ (kernelIsKernel f) (coherentRestriction j)) hf

/-- Equality on the open is witnessed by an actual coherent monomorphism
that is an isomorphism on the open. The witness is the kernel of `f - g`. -/
theorem coherentRestriction_map_eq_iff_denominator {M N : Coherent X} (f g : M ⟶ N) :
    (coherentRestriction j).map f = (coherentRestriction j).map g ↔
      ∃ (M' : Coherent X) (s : M' ⟶ M), Mono s ∧
        (coherentSupportedAway j).isoModSerre s ∧ s ≫ f = s ≫ g := by
  constructor
  · intro hfg
    refine ⟨kernel (f - g), kernel.ι (f - g), inferInstance, ?_, ?_⟩
    · apply coherent_kernel_denominator j
      simp [hfg]
    · have h := kernel.condition (f - g)
      simpa only [Preadditive.comp_sub, sub_eq_zero] using h
  · rintro ⟨M', s, _, hs, hfg⟩
    have : IsIso ((coherentRestriction j).map s) :=
      (coherentSupportedAway_isoModSerre_iff j s).mp hs
    apply (cancel_epi ((coherentRestriction j).map s)).mp
    simpa only [← Functor.map_comp] using congrArg (coherentRestriction j).map hfg

end Quillen.CoherentScheme
