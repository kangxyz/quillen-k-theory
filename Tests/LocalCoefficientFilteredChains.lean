/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.FilteredChains
public import Tests.LocalCoefficientChains

/-!
# Consumers of local chains in filtered realization colimits

The regular path-class system checks that original stage maps generate chains
without assuming constant coefficients. Finite coefficient summands lift through
one common stage, even when stage maps are not injective.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace Quillen.Tests.LocalCoefficientFilteredChains

open LocalCoefficients

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
include hc

/-- Every regular-system chain is an image under original stage pushforwards. -/
theorem regular_chain_has_stage_sum (b : |c.pt|) (V : ModuleCat.{u} ℤ)
    (n : SimplexCategory)
    (x : chainModule (LocalCoefficientChains.regularSystem b V) n) :
    ∃ y, filteredStageChainMap F c (LocalCoefficientChains.regularSystem b V) n y = x :=
  filteredStageChainMap_surjective F c hc _ n x

/-- A finite family of whole coefficient summands factors through one stage. -/
theorem finite_coefficients_have_common_stage (A : System.{u, u} |c.pt|)
    {ι : Type u} [Finite ι] (n : SimplexCategory) (σ : ι → SingularSimplex |c.pt| n) :
    ∃ j, ∃ l : (∐ fun i ↦ simplexFiber A (σ i)) ⟶
      chainModule (pullback (SSet.toTop.map (c.ι.app j)).hom A) n,
      l ≫ pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A n =
        Sigma.desc (fun i ↦ chainInclusion A (σ i)) :=
  filtered_finite_summands_factor F c hc A n σ

end Quillen.Tests.LocalCoefficientFilteredChains
