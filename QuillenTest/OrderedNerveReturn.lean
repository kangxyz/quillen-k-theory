/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.Realization.OrderedNerveRealizationMap

/-! Named regressions for all-mono coherence and the actual return map. -/
@[expose] public section
noncomputable section
open Convexity CategoryTheory Opposite
open scoped Topology Simplicial
universe u v w
namespace QuillenTest.OrderedNerveReturn

open Quillen
open NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- Every injection retains its exact vertex ordering and zero coefficients. -/
theorem arbitrary_mono {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) [Mono φ]
    (v : Fin (m + 1) → A) (hv : AdmissibleVertices E v)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    interpolate E v hv (x.map φ.toOrderHom) =
      interpolate E (v ∘ φ.toOrderHom) (hv.comp φ.toOrderHom) x :=
  interpolate_mono E m φ v hv x

/-- The singleton base case is the actual supplied point. -/
theorem dimension_zero (v : Fin 1 → A) (hv : AdmissibleVertices E v)
    (x : StdSimplex ℝ (Fin 1)) : interpolate E v hv x = v 0 := interpolate_zero E v hv x

/-- Every vertex, including the last, has its exact selected target value. -/
theorem all_vertices {n : ℕ} (v : Fin (n + 1) → A) (hv : AdmissibleVertices E v)
    (i : Fin (n + 1)) : interpolate E v hv (StdSimplex.single i) = v i :=
  interpolate_vertex E v hv i

variable {ι : Type v} [LinearOrder ι] {κ : Type w}
variable (W : ι → Set A) (V : κ → Set A) (hconvex : ∀ k, E.IsConvex (V k))
variable (href : PointStarRefines W V) (vertex : ι → A) (hvertex : ∀ i, vertex i ∈ W i)

/-- Continuity is for the original weak realization topology. -/
theorem actual_return_continuous :
    Continuous (nerveReturnMap E W V hconvex href vertex hvertex) :=
  (nerveReturnMap E W V hconvex href vertex hvertex).continuous

/-- Original nondegenerate simplex charts retain their literal ordered interpolation. -/
theorem nondegenerate_chart (s : (orderedNerve W).toSSet.N)
    (x : StdSimplex ℝ (Fin (s.dim + 1))) :
    nerveReturnMap E W V hconvex href vertex hvertex (realizationSimplex s.simplex x) =
      interpolate E (nerveVertices W vertex s.simplex)
        (nerveVertices_admissible E W V hconvex href vertex hvertex s.simplex) x :=
  nerveReturnMap_nondegenerate E W V hconvex href vertex hvertex s x

/-- All original repeated-vertex weights are summed before target interpolation. -/
theorem original_simplex_aggregated (s : (orderedNerve W).toSSet.S)
    (x : StdSimplex ℝ (Fin (s.dim + 1))) :
    nerveReturnMap E W V hconvex href vertex hvertex (realizationSimplex s.simplex x) =
      interpolate E (nerveVertices W vertex s.toN.simplex)
        (nerveVertices_admissible E W V hconvex href vertex hvertex s.toN.simplex)
        (x.map s.toNπ.toOrderHom) :=
  nerveReturnMap_aggregated E W V hconvex href vertex hvertex s x

/-- Every original chart preserves every carrier, independent of degeneracy and chosen witnesses. -/
theorem every_original_carrier (s : (orderedNerve W).toSSet.S)
    (x : StdSimplex ℝ (Fin (s.dim + 1))) {U : Set A} (hU : E.IsConvex U)
    (hv : ∀ i, nerveVertices W vertex s.simplex i ∈ U) :
    nerveReturnMap E W V hconvex href vertex hvertex (realizationSimplex s.simplex x) ∈ U :=
  nerveReturnMap_mem E W V hconvex href vertex hvertex s x hU hv

end QuillenTest.OrderedNerveReturn
