/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.Gluing
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.AffineExtension

/-!
# Restriction transport used by coherent object extension

These lemmas keep the finite affine-cover induction inside the actual
ambient module sheaf and preserve its restriction to the original open.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

open Scheme.Modules

/-- An isomorphism on an open remains an isomorphism on every smaller open. -/
theorem isIso_restrict_map_of_le
    {X : Scheme.{u}} {W V : X.Opens} (h : W ≤ V)
    {M N : X.Modules} (s : M ⟶ N)
    [IsIso ((restrictFunctor V.ι).map s)] :
    IsIso ((restrictFunctor W.ι).map s) := by
  let e : restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h) ≅
      restrictFunctor W.ι :=
    (restrictFunctorComp (X.homOfLE h) V.ι).symm ≪≫
      restrictFunctorCongr (X.homOfLE_ι h)
  apply (NatIso.isIso_map_iff e s).mp
  exact (restrictFunctor (X.homOfLE h)).map_isIso ((restrictFunctor V.ι).map s)

/-- Restriction along an open immersion and along its actual range have the
same isomorphism-detection property. -/
theorem isIso_restrict_map_of_opensRange
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (s : M ⟶ N)
    [IsIso ((restrictFunctor j.opensRange.ι).map s)] :
    IsIso ((restrictFunctor j).map s) := by
  let e : restrictFunctor j.opensRange.ι ⋙ restrictFunctor j.isoOpensRange.hom ≅
      restrictFunctor j :=
    (restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).symm ≪≫
      restrictFunctorCongr j.isoOpensRange_hom_ι
  apply (NatIso.isIso_map_iff e s).mp
  exact (restrictFunctor j.isoOpensRange.hom).map_isIso
    ((restrictFunctor j.opensRange.ι).map s)

/-- Coherence on the top open is coherence on the scheme itself. -/
theorem affineLocallyFiniteType_of_restrict_top
    {X : Scheme.{u}} (M : X.Modules)
    (h : affineLocallyFiniteType (⊤ : X.Opens).toScheme (M.restrict (⊤ : X.Opens).ι)) :
    affineLocallyFiniteType X M := by
  let e : (M.restrict (⊤ : X.Opens).ι).restrict X.topIso.inv ≅ M :=
    ((restrictFunctorComp X.topIso.inv (⊤ : X.Opens).ι).app M).symm ≪≫
      (restrictFunctorCongr X.toIso_inv_ι).app M ≪≫ restrictFunctorId.app M
  exact (affineLocallyFiniteType X).prop_of_iso e (affineLocallyFiniteType_restrict X.topIso.inv h)

end Quillen.CoherentScheme
