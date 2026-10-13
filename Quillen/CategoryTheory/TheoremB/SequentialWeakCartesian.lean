/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.ReplacementSkeletonCompact
public import Quillen.Topology.HELP.StrictFiniteCriterion

/-!
# Weak-input sequential cartesian assembly

The original stage-to-colimit comparison is weak when each original finite
stage comparison is weak. Compact factorization retains the complete path
family; stage injectivity recovers the exact original boundary square. Only
finite cube HELP is applied. No finite-stage continuous inverse is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Topology
open scoped Topology unitInterval Simplicial
universe u
namespace Quillen.CartesianRealization.Sequential
variable {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
  (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d)
  [∀ n, T1Space (F.obj n)] [∀ n, T1Space (G.obj n)]
  (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
  (hG : ∀ n, IsClosedEmbedding (G.map (homOfLE (Nat.le_succ n))))

include hd hF hG

/-- Full original-boundary strict HELP follows from actual weak finite-stage
comparisons, including the empty boundary of the zero cube. -/
theorem colimitComparison_finiteCubeStrictHELP_of_weakStages (k : ℕ)
    (hstage : ∀ n (h : k ≤ n), IsWeakHomotopyEquivalence (stageComparison η k n h)) :
    FiniteCubeStrictHELP (colimitComparison η c hc d k) := by
  intro q a b w
  obtain ⟨n,h,g,hg⟩ := compact_factors η c hc d hd hF hG k b
  let j := stageToColimit η c hc d k n h
  have hj := stageToColimit_injective η c hc d k n h
    (RealizationCompactStages.stage_isClosedEmbedding hc hF n).injective
    (RealizationCompactStages.stage_isClosedEmbedding hd hG n).injective
  have ws : (stageComparison η k n h).comp a = g.comp (CubicalTests.boundaryInclusion q).hom := by
    apply ContinuousMap.ext
    intro z
    apply hj
    exact (ContinuousMap.congr_fun (stageToColimit_comparison η c hc d k n h) (a z)).trans
      ((ContinuousMap.congr_fun w z).trans
        (ContinuousMap.congr_fun hg ((CubicalTests.boundaryInclusion q) z)).symm)
  obtain ⟨a',ha',⟨K⟩⟩ := (hstage n h).cube_strictHELP q a g ws
  refine ⟨a',ha',⟨(K.compContinuousMap j).cast ?_ hg⟩⟩
  rw [← ContinuousMap.comp_assoc,stageToColimit_comparison]

/-- The actual original stage-to-colimit comparison has the complete weak
property, with no nonempty-source or ordinary-HE premise. -/
theorem colimitComparison_isWeakHomotopyEquivalence_of_weakStages (k : ℕ)
    (hstage : ∀ n (h : k ≤ n), IsWeakHomotopyEquivalence (stageComparison η k n h)) :
    IsWeakHomotopyEquivalence (colimitComparison η c hc d k) :=
  (colimitComparison_finiteCubeStrictHELP_of_weakStages η c hc d hd hF hG k
    hstage).isWeakHomotopyEquivalence

end Quillen.CartesianRealization.Sequential
namespace Quillen.TheoremB
open TheoremA Quillen.CartesianRealization.Sequential
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- The actual replacement skeleton has all separation, closed-embedding,
compact-family, and colimit inputs; only genuine weak finite-stage comparisons
remain for its general natural transformation. -/
theorem replacementSkeletonComparison_isWeakHomotopyEquivalence_of_weakStages (k : ℕ)
    (hstage : ∀ n (h : k ≤ n),
      IsWeakHomotopyEquivalence (stageComparison (realizedReplacementSkeletonMap η) k n h)) :
    IsWeakHomotopyEquivalence (replacementSkeletonComparison η k) :=
  colimitComparison_isWeakHomotopyEquivalence_of_weakStages (realizedReplacementSkeletonMap η)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (realizedReplacementSkeletonCocone J) (realizedReplacementSkeletonIsColimit J)
    (realizedReplacementSkeleton_closedEmbeddings H) (realizedReplacementSkeleton_closedEmbeddings
      J)
    k hstage

end Quillen.TheoremB
