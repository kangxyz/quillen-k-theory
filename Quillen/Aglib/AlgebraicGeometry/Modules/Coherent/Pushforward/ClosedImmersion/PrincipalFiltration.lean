/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.PrincipalImage
public import Quillen.Aglib.Algebra.Category.FGModuleCat.ScalarRepresentation
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.CentralEndomorphism
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis

/-!
# Finite coherent closed-support filtrations

Under the original noetherian hypotheses, genuine closed support produces finite filtrations whose
factors are annihilated by the defining ideal. The actual supported categorical presentations and
their universes are retained.-/
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

open Quillen

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- Geometric vanishing on the principal open is exactly torsion of the
actual global-section module. -/
theorem finiteTypeSheavesSupportedAway_iff_torsion (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (principalOpen R f) M ↔
      torsion (Submonoid.powers f) ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M) := by
  rw [← finiteTypeSheavesRestriction_kernel_eq_support]
  let e := (affinePrincipalRestrictionSquare R f).app
    ((finiteTypeSheavesAffineEquivalence R).functor.obj M)
  change IsZero ((finiteTypeSheavesRestriction (principalOpen R f)).obj M) ↔
    IsZero ((functor (Submonoid.powers f)).obj
      ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M))
  constructor
  · intro h
    exact ((finiteTypeSheavesSpecModuleEquivalence (CommRingCat.of (Localization.Away
      f))).functor.map_isZero h).of_iso e
  · intro h
    exact IsZero.of_full_of_faithful_of_isZero
      (finiteTypeSheavesSpecModuleEquivalence (CommRingCat.of (Localization.Away f))).functor _
      (h.of_iso e.symm)

/-- A single power of f kills every section of a supported coherent sheaf. -/
theorem finiteTypeSheavesSupportedAway_iff_uniform (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (principalOpen R f) M ↔ ∃ n : ℕ,
      ∀ m : (finiteTypeSheavesSpecModuleEquivalence R).functor.obj M, f ^ n • m = 0 := by
  rw [finiteTypeSheavesSupportedAway_iff_torsion, torsion_powers_iff_uniform]

/-- The actual small category used by public principal-open localization. -/
abbrev SmallSupport := (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSmallSupport
  (principalOpen R f)).FullSubcategory

/-- Actual sheaves represented by the compatible support category, followed
by their actual finite global-section modules. -/
abbrev supportRepresentation : SmallSupport R f ⥤ FGModuleCat.{u} R :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSmallSupport (principalOpen R f)).ι ⋙
    (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse ⋙
      (finiteTypeSheavesSpecModuleEquivalence R).functor

instance supportRepresentation_additive : (supportRepresentation R f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (supportRepresentation R f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Scalar multiplication on the genuine small supported coherent category. -/
abbrev supportScalar : 𝟭 (SmallSupport R f) ⟶ 𝟭 (SmallSupport R f) :=
  ScalarRepresentation.scalar (supportRepresentation R f) f

/-- The killed objects inside the genuine small supported coherent category. -/
abbrev supportKilled : ObjectProperty (SmallSupport R f) := killed (supportScalar R f)

theorem supportKilled_iff (M : SmallSupport R f) :
    supportKilled R f M ↔ ∀ m : (supportRepresentation R f).obj M, f • m = 0 :=
  ScalarRepresentation.killed_iff (supportRepresentation R f) f M

/-- Nilpotence follows from genuine support and finite generation. -/
theorem support_power_nilpotent (M : SmallSupport R f) :
    ∃ n : ℕ, power (supportScalar R f) M n = 0 := by
  have h := (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSmallSupport_iff
    (principalOpen R f) M.obj).mp M.property
  obtain ⟨n, hn⟩ := (finiteTypeSheavesSupportedAway_iff_uniform R f _).mp h
  exact ⟨n, ScalarRepresentation.power_eq_zero (supportRepresentation R f) f M n hn⟩

/-- The actual finite image filtration on every supported coherent object. -/
theorem supportFiltrationHypothesis : Devissage.FiltrationHypothesis (supportKilled R f) :=
  PrincipalSupportDevissage.filtrationHypothesis (supportScalar R f) (support_power_nilpotent R f)

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
