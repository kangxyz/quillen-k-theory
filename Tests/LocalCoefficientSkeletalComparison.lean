/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremA.SkeletalHomology

/-! # Original all-dimensional twisted skeletal comparison consumers -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LocalCoefficients Quillen.TheoremA
open scoped Simplicial Topology
universe u
namespace Quillen.Tests
variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}}
  (η : H ⟶ K)
  (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
    QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))

/-- The original stage map, for an arbitrary abelian target local system and every stage. -/
example (n : ℕ) (A : System.{u, u} ((realizedReplacementSkeleton K).obj n))
    (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap ((realizedReplacementSkeletonMap η).app n).hom A) :=
  replacementSkeletonStageMap_abelian_quasiIso η hη n A hA

/-- The empty zero-stage endpoint is included, rather than excluded by the induction. -/
example (A : System.{u, u} ((realizedReplacementSkeleton K).obj 0))
    (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap ((realizedReplacementSkeletonMap η).app 0).hom A) :=
  replacementSkeletonStageMap_abelian_quasiIso η hη 0 A hA

/-- The original cokernel comparison, without replacing it by a shifted homology object. -/
example (n : ℕ) (A : System.{u, u} ((realizedReplacementSkeleton K).obj (n + 1)))
    (hA : AbelianMonodromy A) :
    QuasiIso (embeddingSquareCokernelMap (replacementSkeletonStep H n)
      (replacementSkeletonStep K n) (replacementSkeletonStageMap η n)
      (replacementSkeletonStageMap η (n + 1)) (replacementSkeletonStep_square η n) A) :=
  replacementSkeletonCokernelMap_quasiIso η hη n A hA

end Quillen.Tests
