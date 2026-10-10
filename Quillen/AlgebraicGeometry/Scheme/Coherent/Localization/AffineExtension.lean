/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.AffineApproximation
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.SubobjectPreimage

/-!
# Actual coherent extension inside a quasicoherent affine ambient sheaf

A coherent subsheaf on an arbitrary open of a noetherian affine scheme
extends coherently inside the given quasicoherent ambient sheaf. First take
the actual quasicoherent preimage kernel, then a finite submodule capturing
its restriction on the compact open. No principal-open replacement or
quotient-equivalence hypothesis occurs.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

/-- A coherent subobject on an arbitrary open of a noetherian affine
scheme extends to a coherent subobject of its actual quasicoherent ambient. -/
theorem affineLocallyFiniteType_subobject_extension_affine
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    {U : Scheme.{u}} [IsLocallyNoetherian U]
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (a : A.obj ⟶ M.restrict j) [Mono a] :
    ∃ (B : FiniteTypeSheaves (Spec R)) (b : B.obj ⟶ M), Mono b ∧
      ∃ (e : B.obj.restrict j ≅ A.obj),
        (Scheme.Modules.restrictFunctor j).map b = e.hom ≫ a := by
  obtain ⟨K, s, hK, hs, e, he⟩ := quasicoherent_subobject_preimage j M A a
  have : K.IsQuasicoherent := hK
  have : Mono s := hs
  have hKj : affineLocallyFiniteType U (K.restrict j) := (affineLocallyFiniteType U).prop_of_iso e.symm A.property
  let er : Scheme.Modules.restrictFunctor j ⋙
      Scheme.Modules.restrictFunctor j.isoOpensRange.inv ≅
      Scheme.Modules.restrictFunctor j.opensRange.ι :=
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
      Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp
  have hKr : affineLocallyFiniteType j.opensRange.toScheme (K.restrict j.opensRange.ι) :=
    (affineLocallyFiniteType j.opensRange.toScheme).prop_of_iso (er.app K)
      (affineLocallyFiniteType_restrict j.isoOpensRange.inv hKj)
  obtain ⟨B, t, ht, htr⟩ := exists_coherent_subsheaf_restrict_isIso R K j.opensRange
    (NoetherianSpace.isCompact _) hKr
  have : Mono t := ht
  have : IsIso ((Scheme.Modules.restrictFunctor j.opensRange.ι).map t) := htr
  have hj : j.isoOpensRange.hom ≫ j.opensRange.ι = j := by
    apply (cancel_epi j.isoOpensRange.inv).mp
    simp [← Category.assoc, j.isoOpensRange_inv_comp]
  let er' : Scheme.Modules.restrictFunctor j.opensRange.ι ⋙
      Scheme.Modules.restrictFunctor j.isoOpensRange.hom ≅
      Scheme.Modules.restrictFunctor j :=
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hj
  have htj : IsIso ((Scheme.Modules.restrictFunctor j).map t) := by
    apply (NatIso.isIso_map_iff er' t).mp
    exact (Scheme.Modules.restrictFunctor j.isoOpensRange.hom).map_isIso
      ((Scheme.Modules.restrictFunctor j.opensRange.ι).map t)
  let e' : B.obj.restrict j ≅ A.obj :=
    asIso ((Scheme.Modules.restrictFunctor j).map t) ≪≫ e
  refine ⟨B, t ≫ s, inferInstance, e', ?_⟩
  rw [Functor.map_comp, he]
  rfl

end Quillen.CoherentScheme
