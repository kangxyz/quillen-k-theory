/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Realization.RelativeSphericalStraightening

/-! # Full dimension-two and stationary-face regression checks -/

noncomputable section

open Quillen Convexity
open scoped Topology unitInterval

universe u

variable {Z : Type u} [TopologicalSpace Z] [PathConnectedSpace Z]
    (z : Z) (f₀ : SphericalSimplex Z z 2)
    (b : Finset C(StdSimplex ℝ (Fin 4), Z))
    (hs : ∀ x : Z, Subsingleton (HomotopyGroup.Pi 1 Z x))

/-- The n=2 construction reaches tetrahedra, with all four spherical faces
and a literally stationary arbitrary spherical input. -/
example :
    ∃ P : PartialSimplexStraightening 2 z (sphericalStraighteningFamily f₀ b)
      (sphericalStraighteningFixedFamily f₀) (sphericalStraighteningFamily_faceClosed f₀ b) 4,
      (∀ (s : {s // s ∈ sphericalStraighteningFamily f₀ b 3}) (i : Fin 4),
        ∀ x ∈ simplexBoundary 2,
          P.endpoint 2 ((sphericalStraighteningFamily_faceClosed f₀ b).face s i) x = z) ∧
      (∀ t x, P.homotopy 2
        ⟨f₀.val, sphericalStraighteningFixedFamily_subset f₀ b 2
          (mem_sphericalStraighteningFixedFamily_input f₀)⟩ (t, x) = f₀ x) := by
  obtain ⟨P⟩ := exists_relative_spherical_straightening 2 z f₀ b (by
    intro x k hk hn
    have hk1 : k = 1 := by omega
    subst k
    exact hs x)
  refine ⟨P, ?_, ?_⟩
  · intro s i x hx
    exact (P.sphericalEndpoint (by omega) _).boundary x hx
  · intro t x
    exact P.homotopy_stationary 2 _ (mem_sphericalStraighteningFixedFamily_input f₀) t x

variable (P : PartialSimplexStraightening 2 z (sphericalStraighteningFamily f₀ b)
    (sphericalStraighteningFixedFamily f₀) (sphericalStraighteningFamily_faceClosed f₀ b) 4)

/-- Every edge point of every tetrahedron is collapsed, by genuine barycentric support. -/
example (s : {s // s ∈ sphericalStraighteningFamily f₀ b 3})
    (x : StdSimplex ℝ (Fin 4)) (hx : x.weights.support.card ≤ 2) :
    P.endpoint 3 s x = z := P.endpoint_skeleton 3 (by omega) s x hx

/-- Shared actual triangular faces from distinct support maps have identical
tracks, rather than separately chosen homotopies indexed by occurrences. -/
example (s t : {s // s ∈ sphericalStraighteningFamily f₀ b 3}) (i j : Fin 4)
    (h : singularVertexRestriction s.val i.succAbove =
      singularVertexRestriction t.val j.succAbove)
    (x : StdSimplex ℝ (Fin 3)) (u : I) :
    P.homotopy 3 s (u, x.map i.succAbove) =
      P.homotopy 3 t (u, x.map j.succAbove) := by
  change P.track 3 s (x.map i.succAbove, u) = P.track 3 t (x.map j.succAbove, u)
  rw [P.face 2 (by omega), P.face 2 (by omega)]
  congr 2
  exact Subtype.ext h

/-- Every standard face of the chosen input stays pointwise stationary. -/
example (i : Fin 3) (x : StdSimplex ℝ (Fin 2)) (t : I) :
    P.homotopy 1
      ((sphericalStraighteningFamily_faceClosed f₀ b).face
        ⟨f₀.val, sphericalStraighteningFixedFamily_subset f₀ b 2
          (mem_sphericalStraighteningFixedFamily_input f₀)⟩ i) (t, x) = z := by
  rw [P.homotopy_stationary 1 _
    (sphericalStraighteningFixedFamily_faceClosed f₀ 1 f₀.val
      (mem_sphericalStraighteningFixedFamily_input f₀) i)]
  exact f₀.boundary _ (simplexBoundaryFace 1 i x).property

/-- Both original and endpoint maps are the endpoints of the displayed actual homotopy. -/
example (s : {s // s ∈ sphericalStraighteningFamily f₀ b 3})
    (x : StdSimplex ℝ (Fin 4)) :
    P.homotopy 3 s (0, x) = s.val x ∧ P.homotopy 3 s (1, x) = P.endpoint 3 s x :=
  ⟨(P.homotopy 3 s).apply_zero x, (P.homotopy 3 s).apply_one x⟩
