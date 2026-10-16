/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Category.FGModuleCat.ScalarRepresentation

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.PrincipalFiltration

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.PrincipalImage
public import Quillen.AlgebraicGeometry.Scheme.Coherent.PrincipalLocalization
public import Quillen.Devissage.CentralEndomorphism
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel

/-!
# Actual supported coherent sheaves and their principal image filtrations

The compatible upper-universe small category is the actual kernel of
principal-open restriction. Its fully faithful finite-module representation
allows scalar multiplication even though the sheaf category and ring have
different universes. The resulting nilpotent image filtration is genuine
categorical dévissage, not an equivalence with all supported objects.
-/
@[expose] public section

open ModuleCat.FiniteLocalization
open Quillen.FiniteModuleLocalization
open Quillen.PrincipalSupportDevissage


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
open FiniteModuleLocalization PrincipalSupportDevissage

namespace ScalarRepresentation
variable {C : Type w} [Category.{v} C] [Abelian C]
  {A : Type u} [CommRing A] (F : C ⥤ FGModuleCat.{u} A) [F.Full] [F.Faithful]

variable [F.Additive]

end ScalarRepresentation

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- Genuine dévissage on the actual compatible support category, in the
public upper universe. Its forward map is the canonical killed inclusion. -/
def supportDevissageKEquiv (n : ℕ) :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled R f)).K n ≃*
      CoherentPrincipalSupportedG R f n :=
  Devissage.KEquiv (supportKilled R f) (supportFiltrationHypothesis R f) n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem supportDevissageKEquiv_coe (n : ℕ) :
    ↑(supportDevissageKEquiv R f n) = Devissage.KMap (supportKilled R f) n := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
