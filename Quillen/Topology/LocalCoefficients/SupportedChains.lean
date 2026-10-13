/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SubspaceChains

/-!
# Actual twisted chains supported on a union of path components

If all coefficient fibers outside a path-saturated subset vanish, every
non-small simplex contributes the zero module. The original subspace inclusion
then induces a chain isomorphism. No openness assumption on the subset is used.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Convexity
open scoped Simplicial
universe u v

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- When the discarded coefficient summands vanish, the existing small-chain
projection is also a right inverse to the original inclusion. -/
theorem smallModuleProjection_inclusion_of_support
    (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory)
    (hA : ∀ σ : SingularSimplex X n, ¬ IsCoverSmall U σ → IsZero (simplexFiber A σ)) :
    smallModuleProjection U A n ≫ smallModuleInclusion U A n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro σ
  by_cases hσ : IsCoverSmall U σ
  · simp [smallModuleProjection, chainInclusion, chainModule, hσ]
  · exact (hA σ hσ).eq_of_src _ _

/-- The actual degreewise small-chain inclusion is invertible under the support condition. -/
theorem smallModuleInclusion_isIso_of_support
    (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory)
    (hA : ∀ σ : SingularSimplex X n, ¬ IsCoverSmall U σ → IsZero (simplexFiber A σ)) :
    IsIso (smallModuleInclusion U A n) := by
  refine ⟨⟨smallModuleProjection U A n, ?_, ?_⟩⟩
  · exact smallModuleInclusion_projection U A n
  · exact smallModuleProjection_inclusion_of_support U A n hA

/-- Vanishing of every discarded simplex fiber makes the original chain inclusion an iso. -/
theorem smallChainComplexInclusion_isIso_of_support
    (U : ι → Set X) (A : System.{u, u} X)
    (hA : ∀ (n : SimplexCategory) (σ : SingularSimplex X n),
      ¬ IsCoverSmall U σ → IsZero (simplexFiber A σ)) :
    IsIso (smallChainComplexInclusion U A) := by
  have h : ∀ n : ℕ, IsIso ((smallChainComplexInclusion U A).f n) :=
    fun n ↦ smallModuleInclusion_isIso_of_support U A ⦋n⦌ (hA ⦋n⦌)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A simplex whose first vertex lies in a path-saturated subset lies wholly in it. -/
theorem simplex_range_subset_of_path_saturated (U : Set X)
    (hU : ∀ a ∈ U, ∀ b, Joined a b → b ∈ U)
    {n : SimplexCategory} (σ : SingularSimplex X n)
    (hσ : σ (StdSimplex.single 0) ∈ U) : Set.range σ ⊆ U := by
  rintro _ ⟨t, rfl⟩
  exact hU _ hσ _ ⟨(PathConnectedSpace.somePath (StdSimplex.single 0) t).map σ.continuous⟩

/-- Coefficients supported on a path-saturated subset have exactly its original
subspace chains. The statement retains the actual inclusion-induced chain map. -/
theorem subspaceInclusion_pushforwardChainMap_isIso_of_support (U : Set X)
    (hU : ∀ a ∈ U, ∀ b, Joined a b → b ∈ U) (A : System.{u, u} X)
    (hA : ∀ x, x ∉ U → IsZero (fiber A x)) :
    IsIso (pushforwardChainMap (subspaceInclusion U) A) := by
  have hsmall : IsIso (smallChainComplexInclusion (singletonCover U) A) := by
    apply smallChainComplexInclusion_isIso_of_support
    intro n σ hσ
    apply hA
    intro h
    exact hσ ((isCoverSmall_singletonCover U σ).mpr
      (simplex_range_subset_of_path_saturated U hU σ h))
  rw [← subspaceSmallChainIso_hom_inclusion U A]
  infer_instance

/-- In particular, extension-by-zero coefficients on a path component have
chains canonically equal up to the original inclusion isomorphism. -/
theorem pathComponentInclusion_pushforwardChainMap_isIso_of_support
    (x : X) (A : System.{u, u} X)
    (hA : ∀ y, y ∉ pathComponent x → IsZero (fiber A y)) :
    IsIso (pushforwardChainMap (subspaceInclusion (pathComponent x)) A) :=
  subspaceInclusion_pushforwardChainMap_isIso_of_support (pathComponent x)
    (fun _ ha _ hab ↦ hab.mem_pathComponent ha) A hA

end Quillen.LocalCoefficients
