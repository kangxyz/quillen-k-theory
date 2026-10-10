/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealSupport
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.SupportDevissage
public import Quillen.AlgebraicGeometry.Scheme.Coherent.GlobalLocalization
public import Quillen.Devissage.FiniteCentralFamily

/-!
# Dévissage on actual coherent support for an arbitrary affine ideal

A finite generating family for the ideal acts by genuine natural scalar
endomorphisms on the compatible small supported category. Support proves
objectwise nilpotence. Image filtrations and their pullback refinements have
factors annihilated by the entire ideal.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion.Ideal
open PrincipalSupportDevissage FiniteCentralDevissage
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
  (generators R I).toList.map (ScalarRepresentation.scalar (supportRepresentation R I))

/-- Joint annihilation by those generators. -/
abbrev supportKilled : ObjectProperty (SmallSupport R I) := killedByAll (supportOperators R I)

/-- The finite-family predicate is exactly annihilation by the entire ideal. -/
theorem supportKilled_iff (M : SmallSupport R I) :
    supportKilled R I M ↔
      ∀ r ∈ I, ∀ m : (supportRepresentation R I).obj M, r • m = 0 := by
  change (∀ t ∈ (generators R I).toList.map
    (ScalarRepresentation.scalar (supportRepresentation R I)), killed t M) ↔ _
  simp only [List.forall_mem_map, Finset.mem_toList,
    ScalarRepresentation.killed_iff]
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
  exact ⟨n, ScalarRepresentation.power_eq_zero (supportRepresentation R I) r M n hn⟩

/-- The actual supported coherent category has finite filtrations with
successive quotients annihilated by I. -/
theorem supportFiltrationHypothesis : Devissage.FiltrationHypothesis (supportKilled R I) :=
  FiniteCentralDevissage.filtrationHypothesis (supportOperators R I)
    (supportOperators_nilpotent R I)

/-- The dévissage equivalence on genuine compatible supported G-groups. -/
def supportDevissageKEquiv (n : ℕ) :
    (Devissage.subcategoryExactStructure (supportKilled R I)).K n ≃*
      CoherentGlobalSupportedG (openMap R I) n :=
  Devissage.KEquiv (supportKilled R I) (supportFiltrationHypothesis R I) n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem supportDevissageKEquiv_coe (n : ℕ) :
    ↑(supportDevissageKEquiv R I n) = Devissage.KMap (supportKilled R I) n := rfl

end Quillen.CoherentScheme.ClosedImmersion.Ideal
