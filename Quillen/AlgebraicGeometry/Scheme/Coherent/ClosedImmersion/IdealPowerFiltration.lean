/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.Algebra.Category.FGModuleCat.IdealClosedSupport
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealSupport
public import Quillen.GTheory.FiniteModules.IdealPowerFiltration
public import Quillen.Devissage.FiltrationFunctor

/-!
# Actual ideal-power filtrations of affine coherent sheaves

The actual finite-module tower IⁿM transports through the genuine affine
module/sheaf equivalence to a finite coherent-sheaf filtration. Its quotient
factors are annihilated by I, and its endpoint is the original sheaf.
-/
@[expose] public section

open ModuleCat.FiniteLocalization.IdealClosedSupport
open Quillen.FiniteModuleLocalization.IdealClosedSupport


open AlgebraicGeometry.Scheme.Modules.Coherent
open CategoryTheory.ExactCategory


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
open FiniteModuleLocalization.IdealClosedSupport
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- The actual inverse affine equivalence is exact. -/
def associatedCoherentExact :
    ExactFunctor (finiteModuleExactStructure.{u, u} R) (coherentExactStructure (Spec R)) where
  toFunctor := (finiteTypeSheavesSpecModuleEquivalence R).inverse
  map_conflation _ h := h.map_of_exact _

omit [IsNoetherianRing R] in
/-- The actual associated coherent sheaf of an I-annihilated finite module
is itself annihilated by I. -/
theorem associatedCoherent_killed (M : FGModuleCat.{u} R) (hM : killedBy I M) :
    finiteTypeSheavesKilledBy R I ((finiteTypeSheavesSpecModuleEquivalence R).inverse.obj M) :=
  (killedBy I).prop_of_iso ((finiteTypeSheavesSpecModuleEquivalence R).counitIso.app M).symm hM

/-- Every actual coherent sheaf supported on V(I) has its genuine finite
ideal-power filtration, transported from actual I-power submodules of its
finite global-section module and ending at the original sheaf. -/
theorem coherentIdealPowerFiltration (M : FiniteTypeSheaves (Spec R))
    (hM : finiteTypeSheavesSupportedAway (openMap R I) M) :
    Nonempty ((coherentExactStructure (Spec R)).Filtration (finiteTypeSheavesKilledBy R I) M) := by
  obtain ⟨n, hn⟩ := (finiteTypeSheavesSupportedAway_iff_pow_le_annihilator R I M).mp hM
  obtain ⟨F⟩ := idealPowerFiltration I ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M) n
    hn
  let G := (associatedCoherentExact R).mapFiltration (associatedCoherent_killed R I) F
  exact ⟨G.ofIso ((finiteTypeSheavesSpecModuleEquivalence R).unitIso.app M).symm⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
