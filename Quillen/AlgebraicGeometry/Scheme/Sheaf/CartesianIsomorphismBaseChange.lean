/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.Adjunction.IsomorphismMates
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.IsomorphismFunctors
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChange

/-! # The original cartesian mate for an isomorphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [IsIso f]
/-- Base change of an actual scheme isomorphism retains an invertible original ordinary mate. -/
theorem isIso_cartesianBaseChangeMap_of_isIso : IsIso (cartesianBaseChangeMap a b f j h) := by
  let := h.isIso_snd_of_isIso
  have := pushforward_isEquivalence_of_isIso f
  have := pushforward_isEquivalence_of_isIso b
  exact isIso_mateEquiv_symm_of_equivalences
    (Scheme.Modules.pullbackPushforwardAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction j)
    (TwoSquare.mk _ _ _ _ (cartesianPushforwardSquare a b f j h).hom)
end Quillen.SchemeSheaf
