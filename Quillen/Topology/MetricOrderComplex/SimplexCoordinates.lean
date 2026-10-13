/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.Coordinates
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finite-chain charts in the metric order complex

A chain of vertices sends barycentric weights to their pushforward, adding
weights at repeated vertices. On each finite chain this map is continuous
for the actual L1 metric. These charts respect every simplex operator,
including faces with zero weights and degeneracies with repeated vertices.
-/

@[expose] public section
noncomputable section

open CategoryTheory Convexity Opposite
open scoped Simplicial Topology

universe u v w

namespace Quillen.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only for finite supports. -/
local instance : DecidableEq P := Classical.decEq P

/-- Coordinatewise continuity suffices on one fixed finite support. -/
theorem continuous_of_support_subset {A : Type v} [TopologicalSpace A]
    (f : A → MetricOrderComplex P) (s : Finset P)
    (hs : ∀ a, (f a).weights.support ⊆ s)
    (hf : ∀ v, Continuous (fun a ↦ (f a).weights v)) : Continuous f := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hc : Continuous (fun b ↦ ∑ v ∈ s, dist ((f b).weights v) ((f a).weights v)) := by
    exact continuous_finsetSum _ (fun v _ ↦ (hf v).dist continuous_const)
  have he : ∀ᶠ b in 𝓝 a, ∑ v ∈ s, dist ((f b).weights v) ((f a).weights v) < ε :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
  filter_upwards [he] with b hb
  change coordinateDistance (f b) (f a) < ε
  rwa [coordinateDistance_eq_sum _ _ s (hs b) (hs a)]

/-- Push barycentric coordinates forward along a chain, aggregating repetitions. -/
def chainCoordinates {ι : Type v} (v : ι → P) (hv : IsChain (· ≤ ·) (Set.range v))
    (t : StdSimplex ℝ ι) : MetricOrderComplex P := by
  classical
  refine ⟨t.map v, hv.mono ?_⟩
  intro p hp
  by_contra h
  exact Finsupp.mem_support_iff.mp hp (Finsupp.mapDomain_of_notMem_range t.weights p h)

@[simp]
theorem chainCoordinates_weights {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (t : StdSimplex ℝ ι) :
    (chainCoordinates v hv t).weights = t.weights.mapDomain v := rfl

/-- Positive weights have exactly their image support, even when vertices repeat. -/
theorem chainCoordinates_support {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (t : StdSimplex ℝ ι) :
    (chainCoordinates v hv t).weights.support = t.weights.support.image v := by
  classical
  exact Finsupp.support_mapDomain_of_nonneg t.nonneg v

/-- An injective chain preserves each of its individual barycentric coordinates. -/
theorem chainCoordinates_weights_apply {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (hi : Function.Injective v)
    (t : StdSimplex ℝ ι) (i : ι) :
    (chainCoordinates v hv t).weights (v i) = t.weights i :=
  Finsupp.mapDomain_apply_of_injective hi _ _

@[simp]
theorem chainCoordinates_single {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (i : ι) :
    chainCoordinates v hv (StdSimplex.single i) = vertex (v i) := by
  apply Subtype.ext
  exact StdSimplex.map_single i v

/-- Finite-chain charts are genuinely L1-continuous. -/
@[fun_prop]
theorem continuous_chainCoordinates {ι : Type v} [Finite ι] (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) : Continuous (chainCoordinates v hv) := by
  classical
  let := Fintype.ofFinite ι
  apply continuous_of_support_subset _ (Finset.univ.image v)
  · intro t
    rw [chainCoordinates_support]
    exact Finset.image_subset_image (Finset.subset_univ t.weights.support)
  · intro p
    change Continuous (fun t : StdSimplex ℝ ι ↦ (t.map v).weights p)
    exact (StdSimplex.continuous_weights_apply ℝ p).comp (StdSimplex.continuous_map ℝ v)

/-- A finite-chain chart, bundled as a continuous map. -/
def chainCoordinatesMap {ι : Type v} [Finite ι] (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) : C(StdSimplex ℝ ι, MetricOrderComplex P) :=
  ⟨chainCoordinates v hv, continuous_chainCoordinates v hv⟩

/-- Pushforward along a composite is exactly successive aggregation of weights. -/
theorem chainCoordinates_comp {ι : Type v} {κ : Type w} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (g : κ → ι)
    (hvg : IsChain (· ≤ ·) (Set.range (v ∘ g))) (t : StdSimplex ℝ κ) :
    chainCoordinates v hv (t.map g) = chainCoordinates (v ∘ g) hvg t := by
  apply Subtype.ext
  exact (StdSimplex.map_comp t g v).symm

/-- The metric barycentric chart of an original simplex of the poset nerve. -/
def simplexCoordinates {n : SimplexCategory} (s : (nerve P).obj (op n)) :
    C(StdSimplex ℝ (Fin (n.len + 1)), MetricOrderComplex P) :=
  chainCoordinatesMap s.obj s.monotone.isChain_range

@[simp]
theorem simplexCoordinates_weights {n : SimplexCategory} (s : (nerve P).obj (op n))
    (t : StdSimplex ℝ (Fin (n.len + 1))) :
    (simplexCoordinates s t).weights = t.weights.mapDomain s.obj := rfl

/-- Exact compatibility with every simplex operator, including all degeneracies. -/
theorem simplexCoordinates_naturality {n m : SimplexCategory} (a : n ⟶ m)
    (s : (nerve P).obj (op m)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    simplexCoordinates s (StdSimplex.map a t) =
      simplexCoordinates ((nerve P).map a.op s) t :=
  chainCoordinates_comp s.obj s.monotone.isChain_range a
    (((nerve P).map a.op s).monotone.isChain_range) t

@[simp]
theorem simplexCoordinates_single {n : SimplexCategory} (s : (nerve P).obj (op n))
    (i : Fin (n.len + 1)) :
    simplexCoordinates s (StdSimplex.single i) = vertex (s.obj i) :=
  chainCoordinates_single s.obj s.monotone.isChain_range i

end Quillen.MetricOrderComplex
