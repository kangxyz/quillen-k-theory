/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-!
# Actual coherent restriction denominators

For an open immersion of locally noetherian schemes, restriction inverts
exactly the morphisms with coherent kernel and cokernel supported outside
the open. If two coherent sheaf maps agree on the open, their difference
has a coherent kernel whose inclusion is such a denominator. This proves
the equality/cancellation half of the geometric fraction calculus without
assuming coherent extension or a quotient equivalence.
-/
@[expose] public section

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
theorem finiteTypeSheavesSupportedAway_isoModSerre_iff {M N : FiniteTypeSheaves X} (f : M ⟶ N) :
    (finiteTypeSheavesSupportedAway j).isoModSerre f ↔ IsIso ((finiteTypeSheavesRestriction j).map
      f) := by
  have h : (finiteTypeSheavesSupportedAway j).isoModSerre f ↔
      (finiteTypeSheavesRestriction j).kernel.isoModSerre f := by
    change (finiteTypeSheavesSupportedAway j (kernel f) ∧ finiteTypeSheavesSupportedAway j (cokernel
      f)) ↔ _
    rw [← finiteTypeSheavesRestriction_kernel_eq_support j]
    rfl
  rw [h, Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  rfl

/-- Actual restriction inverts the supported coherent denominators. -/
theorem finiteTypeSheavesRestriction_inverts_support :
    (finiteTypeSheavesSupportedAway j).isoModSerre.IsInvertedBy (finiteTypeSheavesRestriction j) :=
      by
  intro M N f hf
  exact (finiteTypeSheavesSupportedAway_isoModSerre_iff j f).mp hf

/-- A map vanishing after restriction has a genuine coherent kernel
subsheaf which equals its source over the open. -/
theorem coherent_kernel_denominator {M N : FiniteTypeSheaves X} (f : M ⟶ N)
    (hf : (finiteTypeSheavesRestriction j).map f = 0) :
    (finiteTypeSheavesSupportedAway j).isoModSerre (kernel.ι f) := by
  rw [finiteTypeSheavesSupportedAway_isoModSerre_iff]
  exact KernelFork.IsLimit.isIso_ι _
    (KernelFork.mapIsLimit _ (kernelIsKernel f) (finiteTypeSheavesRestriction j)) hf

/-- Equality on the open is witnessed by an actual coherent monomorphism
that is an isomorphism on the open. The witness is the kernel of `f - g`. -/
theorem finiteTypeSheavesRestriction_map_eq_iff_denominator {M N : FiniteTypeSheaves X} (f g : M ⟶
  N) :
    (finiteTypeSheavesRestriction j).map f = (finiteTypeSheavesRestriction j).map g ↔
      ∃ (M' : FiniteTypeSheaves X) (s : M' ⟶ M), Mono s ∧
        (finiteTypeSheavesSupportedAway j).isoModSerre s ∧ s ≫ f = s ≫ g := by
  constructor
  · intro hfg
    refine ⟨kernel (f - g), kernel.ι (f - g), inferInstance, ?_, ?_⟩
    · apply coherent_kernel_denominator j
      simp [hfg]
    · have h := kernel.condition (f - g)
      simpa only [Preadditive.comp_sub, sub_eq_zero] using h
  · rintro ⟨M', s, _, hs, hfg⟩
    have : IsIso ((finiteTypeSheavesRestriction j).map s) :=
      (finiteTypeSheavesSupportedAway_isoModSerre_iff j s).mp hs
    apply (cancel_epi ((finiteTypeSheavesRestriction j).map s)).mp
    simpa only [← Functor.map_comp] using congrArg (finiteTypeSheavesRestriction j).map hfg

end Quillen.CoherentScheme
