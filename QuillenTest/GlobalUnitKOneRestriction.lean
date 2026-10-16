/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneInversion

/-! Actual restriction of rank-one unit classes cancels the inverse of the pulled-back unit. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.GlobalUnitKOneRestriction

/-- The exact original K-map and the inverse actual pulled unit cancel on the structure object. -/
theorem restricted_rankOne_inverse_cancel {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ) :
    perfectKRestrict j 1 (perfectGlobalUnitKOneClass X q (rankOnePerfect X)) *
      perfectGlobalUnitKOneClass U (Units.map j.appTop.hom.toMonoidHom q)⁻¹
        (rankOnePerfect U) = 1 := by
  rw [perfectGlobalUnitKOneClass_restrict_rankOne, perfectGlobalUnitKOneClass_inv]
  exact mul_inv_cancel _

end QuillenTest.GlobalUnitKOneRestriction
