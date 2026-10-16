/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnitInversion


public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison

/-!
# Inversion of original global-unit K-one classes

Inverting a global unit inverts its actual automorphism of a perfect complex and hence its
original normalized K-one class. The restriction corollary retains the canonical zero rebase
of the original K-map and the displayed perfect object, without any nontriviality assumption.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Inversion is preserved by the original, object-component-normalized K-one class. -/
theorem perfectGlobalUnitKOneClass_inv (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : Perfect X) :
    perfectGlobalUnitKOneClass X q⁻¹ K = (perfectGlobalUnitKOneClass X q K)⁻¹ := by
  unfold perfectGlobalUnitKOneClass
  rw [perfectGlobalUnitIso_app_inv]
  exact ((perfectWaldhausen X).automorphismKOneHom K).map_inv
    ((perfectGlobalUnitIso X q).app K)

/-- The actual canonically rebased restriction of an inverse scalar class is the inverse unit
class of the actual restricted object. -/
theorem perfectScalarForwardKOneClass_restrict_inv {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : Perfect X)
    (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑(q⁻¹)) :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q⁻¹ hq) =
      (perfectGlobalUnitKOneClass U q ((perfectRestrict j).obj K))⁻¹ := by
  rw [perfectScalarForwardKOneClass_restrict, perfectGlobalUnitKOneClass_inv]

end Quillen.PerfectComplexes
