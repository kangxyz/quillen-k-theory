/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.ConnectorSimplexFaces

/-! Named regressions for actual finite interpolation and zero-coordinate faces. -/
@[expose] public section

open Quillen.NumerableConnectorCover

noncomputable section
open Convexity
open scoped Topology unitInterval
universe u
namespace QuillenTest.OrderedConnectorInterpolation

open Quillen
open NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- Every geometric carrier witness gives the same actual interpolation map. -/
theorem carrier_witness_independent {n : ℕ} (v : Fin (n + 1) → A)
    (h₁ h₂ : AdmissibleVertices E v) : interpolate E v h₁ = interpolate E v h₂ := rfl

/-- The recursively generated map is continuous for the original finite-simplex topology. -/
theorem actual_continuity {n : ℕ} (v : Fin (n + 1) → A) (h : AdmissibleVertices E v) :
    Continuous (interpolate E v h) := (interpolate E v h).continuous

/-- The map preserves every common carrier, not merely an initially supplied witness. -/
theorem arbitrary_convex_carrier {n : ℕ} (v : Fin (n + 1) → A)
    (h : AdmissibleVertices E v) {V : Set A} (hV : E.IsConvex V)
    (hv : ∀ i, v i ∈ V) (x : StdSimplex ℝ (Fin (n + 1))) :
    interpolate E v h x ∈ V := interpolate_mem E v h hV hv x

/-- The full collapsed cone apex has exactly the first chosen value. -/
theorem first_vertex {n : ℕ} (v : Fin (n + 2) → A) (h : AdmissibleVertices E v) :
    interpolate E v h (StdSimplex.single 0) = v 0 := by
  simpa only [simplexCone_one] using interpolate_cone_one E v h (StdSimplex.single 0)

/-- Zero head mass deletes the head interpolation entirely. -/
theorem head_zero {n : ℕ} (v : Fin (n + 2) → A) (h : AdmissibleVertices E v)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    interpolate E v h (x.map Fin.succ) = interpolate E (v ∘ Fin.succ) (h.comp Fin.succ) x := by
  simpa only [simplexCone_zero] using interpolate_cone_zero E v h x

/-- The middle edge of a triangle has the exact restricted vertex list. -/
theorem triangle_middle (v : Fin 3 → A) (h : AdmissibleVertices E v)
    (x : StdSimplex ℝ (Fin 2)) :
    interpolate E v h (x.map (1 : Fin 3).succAbove) =
      interpolate E (v ∘ (1 : Fin 3).succAbove) (h.comp (1 : Fin 3).succAbove) x :=
  interpolate_face E 1 v h 1 x

/-- All four tetrahedron faces, including the final face, retain their original ordering. -/
theorem tetrahedron_faces (v : Fin 4 → A) (h : AdmissibleVertices E v)
    (i : Fin 4) (x : StdSimplex ℝ (Fin 3)) :
    interpolate E v h (x.map i.succAbove) =
      interpolate E (v ∘ i.succAbove) (h.comp i.succAbove) x :=
  interpolate_face E 2 v h i x

end QuillenTest.OrderedConnectorInterpolation
