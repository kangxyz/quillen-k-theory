/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.Realization.MetricRealizationDomination

/-! Independent consumers require only original local convex geometry. -/
@[expose] public section
noncomputable section
open Convexity
open scoped Topology Simplicial
universe u w
namespace Quillen.Consumer.NumerableRealization
open NumerableConnectorCover
variable {A : Type u} [MetricSpace A]

/-- An arbitrary original open convex cover constructs both maps and their composite homotopy. -/
theorem actual_metric_domination {κ : Type w} (E : LocalEquiconnection A)
    (V : κ → Set A) (hopen : ∀ k, IsOpen (V k)) (hconvex : ∀ k, E.IsConvex (V k))
    (hcover : ∀ x, ∃ k, x ∈ V k) :
    ∃ (K : SSet.{u}) (a : C(A, |K|)) (b : C(|K|, A)),
      Nonempty ((b.comp a).Homotopy (ContinuousMap.id A)) :=
  exists_metric_realization_domination E V hopen hconvex hcover

/-- Pointwise existence of genuine open connector-convex neighborhoods suffices;
no radius, refinement, partition, realization map or domination witness is supplied. -/
theorem actual_domination_of_neighborhoods (E : LocalEquiconnection A)
    (h : ∀ x : A, ∃ V : Set A, IsOpen V ∧ x ∈ V ∧ E.IsConvex V) :
    ∃ (K : SSet.{u}) (a : C(A, |K|)) (b : C(|K|, A)),
      Nonempty ((b.comp a).Homotopy (ContinuousMap.id A)) := by
  choose V hopen hmem hconvex using h
  exact exists_metric_realization_domination E V hopen hconvex (fun x ↦ ⟨x, hmem x⟩)

end Quillen.Consumer.NumerableRealization
