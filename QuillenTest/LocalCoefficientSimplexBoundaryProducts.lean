/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.LocalCoefficients.SimplexBoundaryProducts

/-!
# Original simplex-boundary product comparison consumers

The empty boundary has no coefficient restriction. Positive-dimensional and
all-dimensional clients retain the actual product map and abelian-monodromy
hypotheses, including the induced homology isomorphism in every degree.
-/

open Quillen Quillen.LocalCoefficients CategoryTheory Convexity
universe u

section
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

-- The empty boundary needs no comparison hypothesis and no abelian restriction.
example (f : C(X, Y)) (A : System.{u, u} (Y × simplexBoundary 0)) :
    QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id (simplexBoundary 0))) A) :=
  prodMap_id_simplexBoundary_zero_quasiIso f A

-- The disconnected one-simplex boundary retains arbitrary abelian target systems.
example (f : C(X, Y))
    (hf : ∀ (B : System.{u, u} Y), AbelianMonodromy B → QuasiIso (pushforwardChainMap f B))
    (A : System.{u, u} (Y × simplexBoundary 1)) (hA : AbelianMonodromy A) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (pushforwardChainMap (f.prodMap (ContinuousMap.id (simplexBoundary 1))) A) k) := by
  have := prodMap_id_simplexBoundary_one_quasiIso f hf A hA
  infer_instance

-- The all-dimensional output is the original spatial chain map, in every degree.
example (f : C(X, Y))
    (hf : ∀ (B : System.{u, u} Y), AbelianMonodromy B → QuasiIso (pushforwardChainMap f B))
    (n : ℕ) (A : System.{u, u} (Y × simplexBoundary n)) (hA : AbelianMonodromy A) (k : ℕ) :
    IsIso (pushforwardHomologyMap (f.prodMap (ContinuousMap.id (simplexBoundary n))) A k) := by
  have := prodMap_id_simplexBoundary_quasiIso f hf n A hA
  change IsIso (HomologicalComplex.homologyMap _ k)
  infer_instance
end

-- The overlap in dimension one really is empty, including its topology.
example : IsEmpty (simplexBoundaryOverlap 0) := by
  let := isEmpty_simplexBoundary_zero
  exact ⟨fun x ↦ isEmptyElim (simplexBoundaryOverlapProjection 0 x)⟩
