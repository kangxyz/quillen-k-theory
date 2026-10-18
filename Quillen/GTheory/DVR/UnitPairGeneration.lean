/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.MilnorDvrBoundary
public import Quillen.GTheory.DVR.SplitResidue

/-!
# Actual unit-pair generation for a split-residue local DVR

The group is the original lower finite-module G2 of the actual localization
at a height-one prime. Its generators are the canonically lowered original
scalar products of two units of that local ring.

The actual residue ring section proves original generic injectivity through
the genuine split-residue exact-functor sequence. Surjectivity of the actual
field Milnor map and its original local-boundary compatibility then reduce
every generic class to the proved Milnor unit-symbol span. Original scalar
localization and injectivity reflect those integer combinations back to G2.

No projective DVR K2 identification, arithmetic generic G1 assertion, finite
residue assumption, Matsumoto injectivity, or replacement presentation is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory
open Quillen.FiniteModuleLocalization Quillen.LowDegreeScalarAction
open scoped nonZeroDivisors

namespace Quillen.DvrUnitPairGeneration

/-- The integer span of actual lower G2 products of two original ring units. -/
def unitPairSpan (A : Type u) [CommRing A] [IsNoetherianRing A] :
    Submodule ℤ (Additive (G A 2)) :=
  Submodule.span ℤ {z | ∃ a b : Aˣ, z = Additive.ofMul (DvrSymbols.loweredUnitProduct A a b)}

/-- An actual ring-unit pair belongs to the original unit-pair span. -/
theorem unit_pair_mem (A : Type u) [CommRing A] [IsNoetherianRing A] (a b : Aˣ) :
    Additive.ofMul (DvrSymbols.loweredUnitProduct A a b) ∈ unitPairSpan A :=
  Submodule.subset_span ⟨a, b, rfl⟩

section LocalDvr
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local notation "A" => Localization.AtPrime p.asIdeal
local notation "K₀" => FractionRing (Localization.AtPrime p.asIdeal)
local notation "κ" => p.asIdeal.ResidueField
local instance : IsDiscreteValuationRing A :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _

private def genericLinear : Additive (G A 2) →ₗ[ℤ] Additive (G K₀ 2) :=
  (localizationKMap A⁰ 2).toAdditive.toIntLinearMap

private theorem unitSymbolSpan_le_generic_unitPairSpan :
    MilnorK.K2.DVR.unitSymbolSpan A K₀ ≤
      ((unitPairSpan A).map (genericLinear R p)).comap
        (MilnorDvrBoundary.tensorMilnorToLowerModuleKTwo K₀) := by
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, rfl⟩
  change MilnorDvrBoundary.tensorMilnorToLowerModuleKTwo K₀
    (MilnorK.K2.symbol _ _) ∈ (unitPairSpan A).map (genericLinear R p)
  rw [MilnorDvrBoundary.tensorMilnorToLowerModuleKTwo_symbol]
  apply Submodule.mem_map.mpr
  refine ⟨Additive.ofMul (DvrSymbols.loweredUnitProduct A a b), unit_pair_mem A a b, ?_⟩
  exact congrArg Additive.ofMul (DvrSymbols.loweredUnitProduct_localization A A⁰ a b)

private theorem localDvrBoundary_generic_eq_one (x : G A 2) :
    DedekindLocalDvr.localDvrBoundary R p 1 (localizationKMap A⁰ 2 x) = 1 := by
  have h : localizationKMap A⁰ 2 x ∈ (connectingHom A⁰ 1).ker := by
    rw [← localization_range_eq_connecting_ker]
    exact ⟨x, rfl⟩
  change (DedekindLocalDvr.localResidueSupportKEquiv R p 1).symm
    (connectingHom A⁰ 1 (localizationKMap A⁰ 2 x)) = 1
  rw [show connectingHom A⁰ 1 (localizationKMap A⁰ 2 x) = 1 from h, map_one]

/-- Every original lower G2 class is an integer combination of actual unit pairs,
when the original residue ring map has a genuine ring section. -/
theorem mem_unitPairSpan_of_residueSection (s : κ →+* A)
    (hs : (IsLocalRing.residue A).comp s = RingHom.id κ) (x : G A 2) :
    Additive.ofMul x ∈ unitPairSpan A := by
  obtain ⟨m, hm⟩ := MilnorDvrBoundary.milnorToLowerModuleKTwo_surjective K₀
    (Additive.ofMul (localizationKMap A⁰ 2 x))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have ht : MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ)
      (MilnorK.twoEquiv K₀ m) = 1 := by
    rw [← MilnorDvrBoundary.localDvrBoundary_milnor_det R p hπ, hm]
    change Field.moduleDetEquiv κ
      (((ModuleCat.finiteModuleExactStructure.{u, u} κ).smallKUniverseEquiv.{u, u + 1} 1)
        (DedekindLocalDvr.localDvrBoundary R p 1 (localizationKMap A⁰ 2 x))) = 1
    rw [localDvrBoundary_generic_eq_one, map_one, map_one]
  have hmem : MilnorK.twoEquiv K₀ m ∈ MilnorK.K2.DVR.unitSymbolSpan A K₀ :=
    (MilnorK.K2.DVR.tameValue_eq_one_iff_unitSymbolSpan hπ _).mp ht
  obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp
    (unitSymbolSpan_le_generic_unitPairSpan R p hmem)
  have hym : MilnorDvrBoundary.tensorMilnorToLowerModuleKTwo K₀
      (MilnorK.twoEquiv K₀ m) = MilnorDvrBoundary.milnorToLowerModuleKTwo K₀ m := by
    change MilnorDvrBoundary.milnorToLowerModuleKTwo K₀
      ((MilnorK.twoEquiv K₀).symm (MilnorK.twoEquiv K₀ m)) = _
    rw [LinearEquiv.symm_apply_apply]
  have heq : y = Additive.ofMul x := by
    apply Additive.toMul.injective
    apply SplitResidueDvr.localizationKMap_injective_of_residueSection s hs 2
    exact congrArg Additive.toMul (he.trans (hym.trans hm))
  exact heq ▸ hy

/-- The actual original lower G2 group is generated by these unit-pair classes. -/
theorem unitPairSpan_eq_top_of_residueSection (s : κ →+* A)
    (hs : (IsLocalRing.residue A).comp s = RingHom.id κ) : unitPairSpan A = ⊤ := by
  apply top_unique
  intro x _
  exact mem_unitPairSpan_of_residueSection R p s hs x.toMul

end LocalDvr

end Quillen.DvrUnitPairGeneration
