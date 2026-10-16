/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.ScalarRestrictionPerfect

/-!
# Global-unit automorphisms under open restriction

The perfect scalar of a unit is its original automorphism and the unchanged restriction functor preserves it.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The original perfect scalar of a unit is exactly its existing unit automorphism. -/
theorem perfectGlobalScalar_unit (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ) (K : Perfect X) :
    (perfectGlobalScalar X (↑q)).app K = (perfectGlobalUnitIso X q).hom.app K := by
  apply (locallyPerfect X).ι.map_injective
  rw [perfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  exact complexGlobalScalar_unit X q K.obj

/-- The actual restricted automorphism is multiplication by the literal pulled-back unit. -/
theorem perfectRestrict_globalUnitIso_app {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ) (K : Perfect X) :
    (perfectRestrict j).mapIso ((perfectGlobalUnitIso X q).app K) =
      (perfectGlobalUnitIso U (Units.map j.appTop.hom.toMonoidHom q)).app
        ((perfectRestrict j).obj K) := by
  apply Iso.ext
  change (perfectRestrict j).map ((perfectGlobalUnitIso X q).hom.app K) = _
  rw [← perfectGlobalScalar_unit X q K]
  exact perfectRestrict_scalar_eq_globalUnit j K (↑q)
    (Units.map j.appTop.hom.toMonoidHom q) rfl

end Quillen.PerfectComplexes

end

end
