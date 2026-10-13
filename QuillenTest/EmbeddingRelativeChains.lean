/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.LocalCoefficients.EmbeddingRelativeChains
/-! Original embedding cokernels retain the actual quotient map. -/
noncomputable section
open CategoryTheory Limits Quillen.LocalCoefficients
universe u
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(X, Y)) (hj : Topology.IsEmbedding j) (A : System.{u, u} Y) :
    cokernel (pushforwardChainMap j A) ≅ relativeSingularChainComplex (Set.range j) A :=
  embeddingCokernelIsoRelative j hj A
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(X, Y)) (hj : Topology.IsEmbedding j) (A : System.{u, u} Y) :
    cokernel.π (pushforwardChainMap j A) ≫ (embeddingCokernelIsoRelative j hj A).hom =
      cokernel.π (pushforwardChainMap (subspaceInclusion (Set.range j)) A) :=
  embeddingCokernelIsoRelative_quotient j hj A
