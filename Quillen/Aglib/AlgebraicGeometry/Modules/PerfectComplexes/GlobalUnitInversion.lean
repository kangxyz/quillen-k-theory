/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnit

/-!
# Inversion of the actual perfect global unit

The literal inverse scalar gives the inverse original perfect automorphism.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The literal inverse scalar induces the inverse of the actual perfect automorphism. -/
theorem perfectGlobalUnitIso_app_inv (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : Perfect X) :
    (perfectGlobalUnitIso X q⁻¹).app K = ((perfectGlobalUnitIso X q).app K).symm := by
  apply Iso.ext
  apply (locallyPerfect X).ι.map_injective
  change (locallyPerfect X).ι.map ((perfectGlobalUnitIso X q⁻¹).hom.app K) =
    (locallyPerfect X).ι.map ((perfectGlobalUnitIso X q).inv.app K)
  simp only [perfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  ext n U m
  rfl

end Quillen.PerfectComplexes

end

end
