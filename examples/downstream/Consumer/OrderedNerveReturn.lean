/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.Realization.OrderedNerveRealizationMap

/-! An independent consumer constructs the global return map from geometry alone. -/
@[expose] public section
noncomputable section
open Convexity CategoryTheory Opposite
open scoped Topology Simplicial
universe u v w
namespace Quillen.Consumer.OrderedNerveReturn
open NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] {ι : Type v} [LinearOrder ι] {κ : Type w}

/-- Actual local connector and point-star carrier data construct a continuous map
on the original weak realization, with every original-chart carrier property. -/
theorem exists_return_map (E : LocalEquiconnection A) (W : ι → Set A) (V : κ → Set A)
    (hconvex : ∀ k, E.IsConvex (V k)) (href : PointStarRefines W V)
    (vertex : ι → A) (hvertex : ∀ i, vertex i ∈ W i) :
    ∃ b : C(|(orderedNerve W).toSSet|, A),
      (∀ (s : (orderedNerve W).toSSet.S) (x : StdSimplex ℝ (Fin (s.dim + 1))),
        b (realizationSimplex s.simplex x) =
          interpolate E (nerveVertices W vertex s.toN.simplex)
            (nerveVertices_admissible E W V hconvex href vertex hvertex s.toN.simplex)
            (x.map s.toNπ.toOrderHom)) ∧
      ∀ (s : (orderedNerve W).toSSet.S) (x : StdSimplex ℝ (Fin (s.dim + 1)))
        (U : Set A), E.IsConvex U → (∀ i, vertex (s.simplex.1.obj i) ∈ U) →
          b (realizationSimplex s.simplex x) ∈ U := by
  refine ⟨nerveReturnMap E W V hconvex href vertex hvertex, ?_, ?_⟩
  · exact nerveReturnMap_aggregated E W V hconvex href vertex hvertex
  · intro s x U hU hv
    exact nerveReturnMap_mem E W V hconvex href vertex hvertex s x hU hv

end Quillen.Consumer.OrderedNerveReturn
