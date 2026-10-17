/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealFiltration

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealSupport
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.SupportDevissage
public import Quillen.AlgebraicGeometry.Scheme.Coherent.GlobalLocalization
public import Quillen.Devissage.FiniteCentralFamily
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel

/-!
# Dévissage on actual coherent support for an arbitrary affine ideal

A finite generating family for the ideal acts by genuine natural scalar
endomorphisms on the compatible small supported category. Support proves
objectwise nilpotence. Image filtrations and their pullback refinements have
factors annihilated by the entire ideal.
-/
@[expose] public section

open Quillen.FiniteCentralDevissage
open Quillen.PrincipalSupportDevissage


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
open PrincipalSupportDevissage FiniteCentralDevissage
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- The dévissage equivalence on genuine compatible supported G-groups. -/
def supportDevissageKEquiv (n : ℕ) :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled R I)).K n ≃*
      CoherentGlobalSupportedG (openMap R I) n :=
  Devissage.KEquiv (supportKilled R I) (supportFiltrationHypothesis R I) n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem supportDevissageKEquiv_coe (n : ℕ) :
    ↑(supportDevissageKEquiv R I n) = Devissage.KMap (supportKilled R I) n := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
