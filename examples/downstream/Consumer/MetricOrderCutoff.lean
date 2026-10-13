/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.CutoffHomotopy

/-!
# Independent metric order-complex consumer

For a poset in an arbitrary universe, the actual continuous cutoff is constant
on the specified L1 neighborhood of each vertex. The final example uses the
uncountable inclusion poset of sets of real numbers.
-/

@[expose] public section
noncomputable section

open Quillen Quillen.MetricOrderComplex
open scoped unitInterval

universe u

namespace Consumer.MetricOrderCutoff

/-- Quantitative local constancy at every vertex, with no cardinality restriction. -/
theorem cutoff_eq_vertex_of_dist_lt {P : Type u} [PartialOrder P] (v : P)
    (x : MetricOrderComplex P) (hx : dist x (vertex v) < 1 / 4) :
    cutoffMap x = vertex v := by
  classical
  have hs : x.cutoff.weights.support ⊆ {v} := by
    have := cutoff_support_subset_of_dist_lt (vertex v) x (by simpa using hx)
    simpa using this
  have hv : x.cutoff.weights v = 1 := by
    have ht := x.cutoff.weights_total
    rw [Finsupp.sum_of_support_subset _ hs (fun _ a ↦ a) (by simp)] at ht
    simpa using ht
  apply MetricOrderComplex.ext
  intro w
  change x.cutoff.weights w = (vertex v).weights w
  by_cases hw : w = v
  · subst w
    simpa only [vertex_weights, Finsupp.single_eq_same] using hv
  · have hw' : w ∉ x.cutoff.weights.support := fun h ↦ hw (Finset.mem_singleton.mp (hs h))
    have hz := Finsupp.notMem_support_iff.mp hw'
    simpa only [vertex_weights, Finsupp.single_eq_of_ne hw] using hz

example (A : Set ℝ) (x : MetricOrderComplex (Set ℝ))
    (hx : dist x (vertex A) < 1 / 4) : cutoffMap x = vertex A :=
  cutoff_eq_vertex_of_dist_lt A x hx

-- The homotopy is an actual continuous-map homotopy fixed at this arbitrary basepoint.
example (A : Set ℝ) (t : I) : cutoffHomotopy (t, vertex A) = vertex A :=
  cutoffHomotopy_vertex t A

example (x : MetricOrderComplex (Set ℝ)) (t : I) :
    (cutoffHomotopy (t, x)).weights.support ⊆ x.weights.support :=
  cutoffBlend_support_subset t x

end Consumer.MetricOrderCutoff
