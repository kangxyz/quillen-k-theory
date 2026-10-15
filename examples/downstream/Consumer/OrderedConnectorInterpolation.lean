/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.ConnectorSimplexFaces
public import Quillen.Topology.Realization.OrderedCoverNerve
public import Quillen.Topology.Realization.NumerableConnectorCover

/-! Independent clients construct actual finite simplex maps from geometric data only. -/
@[expose] public section

open Quillen.NumerableConnectorCover

noncomputable section
open Convexity CategoryTheory Opposite
open scoped Topology unitInterval Simplicial
universe u v w
namespace Quillen.Consumer.OrderedConnectorInterpolation
open NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- Any finite vertex family in a convex set has an actual continuous interpolation
with all elementary increasing-face equations, without supplying any extension. -/
theorem finite_family_with_faces {n : ℕ} (v : Fin (n + 2) → A)
    {V : Set A} (hV : E.IsConvex V) (hv : ∀ i, v i ∈ V) :
    ∃ f : C(StdSimplex ℝ (Fin (n + 2)), A), (∀ x, f x ∈ V) ∧
      ∀ (i : Fin (n + 2)) (x : StdSimplex ℝ (Fin (n + 1))),
        f (x.map i.succAbove) =
          interpolate E (v ∘ i.succAbove) ⟨V, hV, fun j ↦ hv (i.succAbove j)⟩ x := by
  let h : AdmissibleVertices E v := ⟨V, hV, hv⟩
  exact ⟨interpolate E v h, interpolate_mem E v h hV hv,
    fun i x ↦ interpolate_face E n v h i x⟩

/-- An actual ordered-cover simplex supplies the required geometric carrier and hence a map.
This does not yet claim compatibility of degenerate simplex interpolation. -/
def cover_simplex_map {ι : Type v} [LinearOrder ι] {κ : Type w}
    (W : ι → Set A) (V : κ → Set A) (hV : ∀ k, E.IsConvex (V k))
    (href : PointStarRefines W V) (vertex : ι → A) (hv : ∀ i, vertex i ∈ W i)
    {n : ℕ} (s : (orderedNerve W).toSSet.obj (op ⦋n⦌)) :
    C(StdSimplex ℝ (Fin (n + 1)), A) :=
  interpolate E (fun j ↦ vertex (s.1.obj j)) (by
    obtain ⟨x, hx⟩ := s.2
    obtain ⟨k, hk⟩ := href x
    exact ⟨V k, hV k, fun j ↦ hk ⟨s.1.obj j, hx j, hv (s.1.obj j)⟩⟩)

end Quillen.Consumer.OrderedConnectorInterpolation
