/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.Fullness

/-!
# The actual quasicoherent preimage of a coherent open subsheaf

The ambient sheaf is allowed to be infinitely generated. Taking the kernel
of its adjoint map to the open quotient extends the given open subsheaf as
a quasicoherent subsheaf. Finite approximation is a subsequent step.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme

/-- The quasicoherent preimage kernel of an actual coherent open subsheaf.
No finite generation of the ambient module sheaf is assumed. -/
theorem quasicoherent_subobject_preimage
    {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (M : X.Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (i : A.obj ⟶ M.restrict j) [Mono i] :
    ∃ (K : X.Modules) (s : K ⟶ M), K.IsQuasicoherent ∧ Mono s ∧
      ∃ (e : K.restrict j ≅ A.obj),
        (Scheme.Modules.restrictFunctor j).map s = e.hom ≫ i := by
  let F := Scheme.Modules.restrictFunctor j
  let adj := Scheme.Modules.restrictAdjunction j
  let C := cokernel i
  have : C.IsQuasicoherent := quasicoherent_cokernel i
  have : ((Scheme.Modules.pushforward j).obj C).IsQuasicoherent :=
    quasicoherent_pushforward_open_of_locallyNoetherian j C
  let k : M ⟶ (Scheme.Modules.pushforward j).obj C := adj.homEquiv M C (cokernel.π i)
  have hk : F.map k ≫ adj.counit.app C = cokernel.π i := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj.homEquiv M C).symm_apply_apply (cokernel.π i)
  let h₁ := isKernelCompMono
    (KernelFork.mapIsLimit _ (kernelIsKernel k) F) (adj.counit.app C) hk.symm
  let h₂ := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)
  refine ⟨kernel k, kernel.ι k, quasicoherent_kernel k, inferInstance,
    h₁.conePointUniqueUpToIso h₂, ?_⟩
  exact (h₁.conePointUniqueUpToIso_hom_comp h₂ WalkingParallelPair.zero).symm

end Quillen.CoherentScheme
