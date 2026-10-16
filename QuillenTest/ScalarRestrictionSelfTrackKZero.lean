/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarRestrictionSelfTrackKZero

/-! # The original scalar restriction and separate cofiber inverse consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.ScalarRestrictionSelfTrackKZero
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : Perfect X) (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original restriction of the original forward scalar class has the forward operation. -/
theorem original_forward_restriction :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q hq) =
      originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) 0 ((perfectWaldhausen X).kZeroObjectClass K) :=
  perfectScalarForwardKOneClass_restrict_selfTrack j K r q hq

/-- The original cofiber orientation contributes exactly the existing inverse. -/
theorem original_cofiber_inverse :
    perfectOpenKRestrict j 1 (perfectScalarCofiberBoundaryKOneClass j K r q hq) =
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) 0 ((perfectWaldhausen X).kZeroObjectClass K))⁻¹ :=
  perfectScalarCofiberBoundaryKOneClass_restrict_selfTrack j K r q hq

end QuillenTest.ScalarRestrictionSelfTrackKZero
