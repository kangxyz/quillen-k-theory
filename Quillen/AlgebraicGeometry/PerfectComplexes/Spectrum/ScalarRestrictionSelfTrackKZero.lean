/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitSelfTrackKZero

/-! # The original restricted scalar class and the actual object self-track operation

The old forward scalar class restricts to the actual flat-unit operation on the
original K-zero object class. The original restriction/flat-pullback isomorphism
is retained explicitly. The original cofiber orientation is a separate inverse
consequence; no all-degree boundary equation is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : Perfect X) (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- The old restricted forward scalar class is the actual original flat-unit object operation. -/
theorem perfectScalarForwardKOneClass_restrict_selfTrack :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q hq) =
      originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) 0 ((perfectWaldhausen X).kZeroObjectClass K) := by
  exact (perfectScalarForwardKOneClass_restrict j K r q hq).trans
    ((perfectGlobalUnitKOneClass_iso U q ((perfectRestrictIsoFlatPullback j).app K)).trans
      (perfectFlatUnitHomotopy_object j q K).symm)

include hq in
/-- The same original cofiber class retains its proved inverse orientation after restriction. -/
theorem perfectScalarCofiberBoundaryKOneClass_restrict_selfTrack :
    perfectOpenKRestrict j 1 (perfectScalarCofiberBoundaryKOneClass j K r q hq) =
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) 0 ((perfectWaldhausen X).kZeroObjectClass K))⁻¹ := by
  rw [perfectScalarCofiberBoundaryKOneClass_eq_inv, map_inv,
    perfectScalarForwardKOneClass_restrict_selfTrack]

end Quillen.PerfectComplexes
