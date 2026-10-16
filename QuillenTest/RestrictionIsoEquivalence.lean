/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.RestrictionIsoEquivalence

/-! The extracted original equivalence retains both literal restriction K-maps. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
universe u
namespace QuillenTest.RestrictionIsoEquivalence

/-- The forward map is exactly the original geometric restriction and its canonical rebase. -/
theorem equivalence_forward_is_original {U X : Scheme.{u}} (e : U ≅ X) (n : ℕ) :
    (perfectKRestrictIsoEquiv e n).toMonoidHom = perfectKRestrict e.hom n := rfl

/-- The inverse map is exactly restriction by the original inverse scheme isomorphism. -/
theorem equivalence_inverse_is_original {U X : Scheme.{u}} (e : U ≅ X) (n : ℕ) :
    (perfectKRestrictIsoEquiv e n).symm.toMonoidHom = perfectKRestrict e.inv n := rfl

/-- The actual original maps cancel, including in connective degree zero. -/
theorem original_inverse_restriction_cancel {U X : Scheme.{u}} (e : U ≅ X) (n : ℕ)
    (x : PerfectK X n) :
    perfectKRestrict e.inv n (perfectKRestrict e.hom n x) = x :=
  (perfectKRestrictIsoEquiv e n).symm_apply_apply x

end QuillenTest.RestrictionIsoEquivalence
