/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.ScalarRestriction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction

/-!
# Restriction of the original perfect scalar

When the scalar becomes the specified unit, the literal perfect restriction map is its genuine unit automorphism.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : Perfect X) (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- The original relative scalar arrow restricts to the actual independent fine unit arrow. -/
theorem perfectRestrict_scalar_eq_globalUnit :
    (perfectRestrict j).map ((perfectGlobalScalar X r).app K) =
      (perfectGlobalUnitIso U q).hom.app ((perfectRestrict j).obj K) := by
  apply (locallyPerfect U).ι.map_injective
  rw [perfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  exact restrict_map_complexGlobalScalar_unit j r q hq K.obj

end Quillen.PerfectComplexes

end

end
