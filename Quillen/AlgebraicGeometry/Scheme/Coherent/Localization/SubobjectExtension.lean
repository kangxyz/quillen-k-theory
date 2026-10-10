/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.QuasicoherentClosure
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.Subobjects
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.GraphFractions

/-!
# Canonical coherent subobject extension by an actual sheaf kernel

Given an open subsheaf `A ⊆ H|U`, take the kernel of the adjoint map
`H → j_* coker(A → H|U)`. Restriction of this kernel is exactly `A`.
When this one pushforward is quasicoherent, the kernel is quasicoherent and
its embedding into the coherent `H` proves coherence.

The quasicoherence of open pushforward is an explicit remaining geometric
input, not a quotient-equivalence assumption or an asserted instance.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual preimage kernel extends a coherent subobject, provided the
pushforward of its quasicoherent cokernel is quasicoherent. -/
theorem affineLocallyFiniteType_subobject_extension_of_quasicoherent_pushforward
    (H : FiniteTypeSheaves X) (A : FiniteTypeSheaves U) (i : A ⟶ (finiteTypeSheavesRestriction
      j).obj H)
    [Mono i]
    [((Scheme.Modules.pushforward j).obj (cokernel i.hom)).IsQuasicoherent] :
    ∃ (H' : FiniteTypeSheaves X) (s : H' ⟶ H), Mono s ∧
      ∃ (e : (finiteTypeSheavesRestriction j).obj H' ≅ A),
        (finiteTypeSheavesRestriction j).map s = e.hom ≫ i := by
  let F := Scheme.Modules.restrictFunctor j
  let adj := Scheme.Modules.restrictAdjunction j
  have : Mono i.hom := (finiteTypeSheavesToModules U).map_mono i
  let C := cokernel i.hom
  let k : H.obj ⟶ (Scheme.Modules.pushforward j).obj C :=
    adj.homEquiv H.obj C (cokernel.π i.hom)
  have hk : F.map k ≫ adj.counit.app C = cokernel.π i.hom := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj.homEquiv H.obj C).symm_apply_apply (cokernel.π i.hom)
  have : (kernel k).IsQuasicoherent := quasicoherent_kernel k
  let H' : FiniteTypeSheaves X :=
    ⟨kernel k, affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι k) H.property⟩
  let s : H' ⟶ H := ObjectProperty.homMk (kernel.ι k)
  have hs : Mono s := by
    apply (finiteTypeSheavesToModules X).mono_of_mono_map
    exact inferInstanceAs (Mono (kernel.ι k))
  let h₁ := isKernelCompMono
    (KernelFork.mapIsLimit _ (kernelIsKernel k) F) (adj.counit.app C) hk.symm
  let h₂ := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i.hom)
  let e : F.obj (kernel k) ≅ A.obj := h₁.conePointUniqueUpToIso h₂
  have he : e.hom ≫ i.hom = F.map (kernel.ι k) :=
    h₁.conePointUniqueUpToIso_hom_comp h₂ WalkingParallelPair.zero
  let e' : (finiteTypeSheavesRestriction j).obj H' ≅ A :=
    (affineLocallyFiniteType U).fullyFaithfulι.preimageIso e
  refine ⟨H', s, hs, e', ?_⟩
  apply (finiteTypeSheavesToModules U).map_injective
  exact he.symm

/-- Quasicoherent open pushforward, once proved geometrically, suffices for
fullness of the genuine coherent support quotient. -/
theorem quotientCoherentRestriction_full_of_quasicoherent_pushforward
    (hPush : ∀ (M : U.Modules), M.IsQuasicoherent →
      ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent) :
    (quotientCoherentRestriction j).Full := by
  apply quotientCoherentRestriction_full_of_subobject_extension j
  intro H A i hi
  have : Mono i := hi
  have : (cokernel i.hom).IsQuasicoherent := quasicoherent_cokernel i.hom
  have : ((Scheme.Modules.pushforward j).obj (cokernel i.hom)).IsQuasicoherent :=
    hPush _ inferInstance
  exact affineLocallyFiniteType_subobject_extension_of_quasicoherent_pushforward j H A i

end Quillen.CoherentScheme
