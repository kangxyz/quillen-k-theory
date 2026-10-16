/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality

/-! The original restriction equivalence of a scheme isomorphism, independent of native Phi. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine

/-- Original geometric restriction through a scheme isomorphism is an actual K-equivalence. -/
def perfectKRestrictIsoEquiv {U X : Scheme.{u}} (e : U ≅ X) (n : ℕ) :
    PerfectK X n ≃* PerfectK U n where
  toFun := perfectKRestrict e.hom n
  invFun := perfectKRestrict e.inv n
  left_inv x := by
    change ((perfectKRestrict e.inv n).comp (perfectKRestrict e.hom n)) x = x
    rw [← perfectKRestrict_comp]
    simp only [e.inv_hom_id, perfectKRestrict_id, MonoidHom.id_apply]
  right_inv x := by
    change ((perfectKRestrict e.hom n).comp (perfectKRestrict e.inv n)) x = x
    rw [← perfectKRestrict_comp]
    simp only [e.hom_inv_id, perfectKRestrict_id, MonoidHom.id_apply]
  map_mul' := (perfectKRestrict e.hom n).map_mul

end Quillen.PerfectComplexes.ProjectiveLine
