/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.GTheory.Dedekind.Localization
public import Quillen.GTheory.Dedekind.ResidueFieldAssembly

/-! Finite residue-family lifting and the resulting original ambient pushforward relation. -/
@[expose] public section

noncomputable section

open Quillen Quillen.DedekindPrimary Quillen.DedekindResidue
open scoped nonZeroDivisors DirectSum

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts Classical.propDecidable

namespace Consumer.DedekindResidueSupport

universe u

/-- A finite residue family lifts through the actual boundary, and its original ambient
pushforwards sum to zero under the explicit generic G1-injectivity premise. -/
theorem finiteResidueLiftWithPushforwardRelation
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (hinj : Function.Injective (FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) 1))
    (a : ⨁ p, Additive (ResidueFieldK R p 1)) :
    ∃ b : FiniteModuleLocalization.G (Localization (nonZeroDivisors R)) 2,
      FiniteModuleLocalization.connectingHom (nonZeroDivisors R) 1 b =
          (residueFieldK1AssemblyEquiv R a).toMul ∧
        ∑ p ∈ a.support,
          Additive.ofMul ((residueFieldPushforwardExact R p).smallKMap 1 (a p).toMul) = 0 := by
  obtain ⟨b, hb⟩ := boundaryG2_surjective_of_genericG1_injective R hinj
    (residueFieldK1AssemblyEquiv R a).toMul
  refine ⟨b, hb, ?_⟩
  have h := supportedKMap_residueFieldAssembly_eq_sum R 0 a
  rw [supportedKMap_eq_one_of_localization_injective R 1 hinj] at h
  exact h.symm

end Consumer.DedekindResidueSupport
