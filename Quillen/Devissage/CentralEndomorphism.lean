/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Category.FGModuleCat.PrincipalSupportSmallModel
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.CentralEndomorphism
public import Quillen.Devissage.Homotopical
public import Quillen.GTheory.FiniteModules.LocalizationSequence

/-!
# Dévissage for a locally nilpotent central endomorphism

A natural endomorphism of the identity gives a genuine dévissage property:
objects on which it vanishes. Its powers give actual finite image filtrations.
This construction will be applied to multiplication by an element on the
category of finite modules supported on its principal closed subset.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.FiniteModuleLocalization

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R)

/-- Classical dévissage for the canonical killed-by-`f` inclusion. This is an
isomorphism on K-groups, and does not identify the two abelian categories. -/
def principalDevissageKEquiv (n : ℕ) :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure (principalKilled f)).K n ≃*
      SupportedG (Submonoid.powers f) n :=
  Devissage.KEquiv (principalKilled f) (principalFiltrationHypothesis f) n

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem principalDevissageKEquiv_coe (n : ℕ) :
    (↑(principalDevissageKEquiv f n) : (CategoryTheory.ObjectProperty.subcategoryExactStructure
      (principalKilled
        f)).K n →* SupportedG (Submonoid.powers f) n) = Devissage.KMap (principalKilled f) n := rfl


/-- Bijectivity includes the genuine homotopical degree zero. -/
theorem principalDevissageKMap_bijective (n : ℕ) :
    Function.Bijective (Devissage.KMap (principalKilled f) n) :=
  (principalDevissageKEquiv f n).bijective

end Quillen.FiniteModuleLocalization
