/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnitRestriction


public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison

/-!
# Original global-unit K-one classes under open restriction

The actual perfect global scalar of a unit is its original unit automorphism. The unchanged
restriction functor maps that automorphism to multiplication by the actual pulled-back unit.
The original canonically rebased K-map therefore preserves its fine K-one class, including the
original rank-one structure sheaf and its displayed restriction isomorphism.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes

/-- The original K-map, with its canonical zero rebase, preserves the actual unit class. -/
theorem perfectGlobalUnitKOneClass_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ) (K : Perfect X) :
    perfectKRestrict j 1 (perfectGlobalUnitKOneClass X q K) =
      perfectGlobalUnitKOneClass U (Units.map j.appTop.hom.toMonoidHom q)
        ((perfectRestrict j).obj K) := by
  unfold perfectGlobalUnitKOneClass perfectKRestrict
  rw [KMap_automorphismKOneClass, perfectRestrict_globalUnitIso_app]

/-- The rank-one formula keeps the original structure-sheaf restriction isomorphism. -/
theorem perfectGlobalUnitKOneClass_restrict_rankOne {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ) :
    perfectKRestrict j 1 (perfectGlobalUnitKOneClass X q (rankOnePerfect X)) =
      perfectGlobalUnitKOneClass U (Units.map j.appTop.hom.toMonoidHom q)
        (rankOnePerfect U) := by
  rw [perfectGlobalUnitKOneClass_restrict]
  exact perfectGlobalUnitKOneClass_iso _ _ (rankOnePerfectRestrictIso j)

end Quillen.PerfectComplexes
