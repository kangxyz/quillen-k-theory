/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.RelativeSphericalStraightening

/-!
# Actual spherical faces of a simplex with collapsed geometric skeleton

This is a representative-level interface for homotopy addition: the face map
is literally the standard increasing singular face, and sphericity follows
from the support-cardinality description of the genuine geometric skeleton.
No homotopy-addition identity is assumed or proved in this owner.
-/

@[expose] public section
noncomputable section

open Convexity

universe u

namespace Quillen

/-- A boundary point has at most d nonzero coordinates among its d+1 vertices. -/
theorem simplexBoundary_subset_skeleton (d : ℕ) :
    simplexBoundary d ⊆ simplexSkeleton d d := by
  classical
  intro x hx
  obtain ⟨i, hi⟩ := hx
  have hs : x.weights.support ⊆ Finset.univ.erase i := by
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hji
    subst j
    exact (Finsupp.mem_support_iff.mp hj) hi
  have hc := Finset.card_le_card hs
  simpa [mem_simplexSkeleton] using hc

/-- The boundary is exactly the highest proper geometric skeleton. -/
theorem simplexBoundary_eq_skeleton (d : ℕ) : simplexBoundary d = simplexSkeleton d d :=
  Set.Subset.antisymm (simplexBoundary_subset_skeleton d)
    (simplexSkeleton_subset_boundary le_rfl)

variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

/-- Every standard face of a simplex with collapsed (n-1)-skeleton is spherical.
The actual underlying map is the original increasing vertex restriction. -/
def sphericalFace (τ : C(StdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ simplexSkeleton n (n + 1), τ x = z) (i : Fin (n + 2)) :
    SphericalSimplex Z z n :=
  ⟨singularVertexRestriction τ i.succAbove, fun x hx ↦
    hτ _ ((simplex_map_mem_skeleton_iff i.succAbove Fin.succAbove_right_injective x).mpr
      (simplexBoundary_subset_skeleton n hx))⟩

@[simp] theorem sphericalFace_apply (τ : C(StdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ simplexSkeleton n (n + 1), τ x = z) (i : Fin (n + 2))
    (x : StdSimplex ℝ (Fin (n + 1))) : sphericalFace τ hτ i x = τ (x.map i.succAbove) := rfl

/-- H4's endpoint face equality identifies the actual H3 spherical face with
the selected lower endpoint, including the entire parametrization. -/
theorem PartialSimplexStraightening.sphericalFace_endpoint {N : ℕ}
    {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}
    (P : PartialSimplexStraightening n z S F hS N) (hn : n + 1 < N)
    (τ : {τ // τ ∈ S (n + 1)}) (i : Fin (n + 2)) :
    sphericalFace (P.endpoint (n + 1) τ) (P.endpoint_skeleton (n + 1) hn τ) i =
      P.sphericalEndpoint (by omega) (hS.face τ i) := by
  apply SphericalSimplex.ext
  intro x
  exact P.face n hn τ i x 1

end Quillen
