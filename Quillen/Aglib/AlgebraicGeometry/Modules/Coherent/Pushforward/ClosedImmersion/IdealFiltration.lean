/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealSupport
public import Quillen.Aglib.Algebra.Category.FGModuleCat.ScalarRepresentation
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.FiniteCentralFamily
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis

/-!
# Finite coherent closed-support filtrations

Under the original noetherian hypotheses, genuine closed support produces finite filtrations whose factors are annihilated by the defining ideal. The actual supported categorical presentations and their universes are retained.
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

open Quillen

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- A finite list genuinely generating the ideal. -/

def generators : Finset R := I.fg_of_isNoetherianRing.choose
@[simp] theorem span_generators : Ideal.span (generators R I : Set R) = I :=
  I.fg_of_isNoetherianRing.choose_spec

theorem generator_mem {r : R} (hr : r ∈ generators R I) : r ∈ I := by
  rw [← span_generators R I]
  exact Ideal.subset_span hr

/-- The actual small supported category used by global open localization. -/

abbrev SmallSupport := (coherentGlobalSmallSupport (openMap R I)).FullSubcategory

/-- Its faithful actual finite-global-sections representation. -/

abbrev supportRepresentation : SmallSupport R I ⥤ FGModuleCat.{u} R :=
  (coherentGlobalSmallSupport (openMap R I)).ι ⋙
    (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse ⋙
      (finiteTypeSheavesSpecModuleEquivalence R).functor

instance supportRepresentation_additive : (supportRepresentation R I).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (supportRepresentation R I)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Scalar actions of the finite generating list, as actual natural maps. -/

def supportOperators : List (𝟭 (SmallSupport R I) ⟶ 𝟭 (SmallSupport R I)) :=
  (generators R I).toList.map
    (Principal.ScalarRepresentation.scalar (supportRepresentation R I))

/-- Joint annihilation by those generators. -/

abbrev supportKilled : ObjectProperty (SmallSupport R I) := killedByAll (supportOperators R I)

/-- The finite-family predicate is exactly annihilation by the entire ideal. -/

theorem supportKilled_iff (M : SmallSupport R I) :
    supportKilled R I M ↔
      ∀ r ∈ I, ∀ m : (supportRepresentation R I).obj M, r • m = 0 := by
  change (∀ t ∈ (generators R I).toList.map
    (Principal.ScalarRepresentation.scalar (supportRepresentation R I)), killed t M) ↔ _
  simp only [List.forall_mem_map, Finset.mem_toList,
    Principal.ScalarRepresentation.killed_iff]
  constructor
  · intro h
    have hI : I ≤ Module.annihilator R ((supportRepresentation R I).obj M) := by
      rw (occs := .pos [1]) [← span_generators R I]
      apply Ideal.span_le.mpr
      intro r hr
      exact Module.mem_annihilator.mpr (h r hr)
    intro r hr
    exact Module.mem_annihilator.mp (hI hr)
  · intro h r hr
    exact h r (generator_mem R I hr)

/-- Genuine support makes every ideal generator nilpotent on each coherent
object. No exponent uniform in the object is used. -/

theorem supportOperators_nilpotent (M : SmallSupport R I) :
    ∀ t ∈ supportOperators R I, ∃ n : ℕ, power t M n = 0 := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  have hM := (coherentGlobalSmallSupport_iff (openMap R I) M.obj).mp M.property
  obtain ⟨n, hn⟩ := supported_power_annihilates R I _ hM r
    (generator_mem R I (Finset.mem_toList.mp hr))
  exact ⟨n,
    Principal.ScalarRepresentation.power_eq_zero (supportRepresentation R I) r M n hn⟩

/-- The actual supported coherent category has finite filtrations with
successive quotients annihilated by I. -/

theorem supportFiltrationHypothesis : Devissage.FiltrationHypothesis (supportKilled R I) :=
  FiniteCentralDevissage.filtrationHypothesis (supportOperators R I)
    (supportOperators_nilpotent R I)

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
