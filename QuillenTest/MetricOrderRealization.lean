/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.Reconstruction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Repeated vertices and zero-coordinate faces in the original realization

These tests compute the actual coordinate map on a degenerate simplex:
`(1/2, 1/3, 1/6)` at `(0, 0, 1)` becomes `(5/6, 1/6)`.
A separate test removes the zero middle coordinate of a two-simplex and
checks its exact realization face equation.
-/

@[expose] public section
noncomputable section

open CategoryTheory Convexity Quillen Quillen.MetricOrderComplex
open scoped Simplicial

namespace QuillenTest.MetricOrderRealization

/-- A three-coordinate test distribution. -/
def sample : StdSimplex ℝ (Fin 3) where
  weights := Finsupp.single 0 (1 / 2) + Finsupp.single 1 (1 / 3) + Finsupp.single 2 (1 / 6)
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Finsupp.sum_add_index]

/-- The increasing edge from zero to one. -/
def edge : (nerve ℕ) _⦋1⦌ :=
  (show Monotone (fun i : Fin 2 ↦ (i : ℕ)) from fun _ _ h ↦ h).functor

/-- Repeat the first vertex using an actual degeneracy of the nerve. -/
def repeated : (nerve ℕ) _⦋2⦌ := (nerve ℕ).σ 0 edge

/-- The two original zero-vertex weights are added, not discarded. -/
theorem repeated_weights :
    (realizationCoordinates (realizationSimplex repeated sample)).weights =
      Finsupp.single 0 (5 / 6) + Finsupp.single 1 (1 / 6) := by
  rw [realizationCoordinates_simplex_weights]
  norm_num [sample, Finsupp.mapDomain_add, Finsupp.mapDomain_single, repeated,
    nerve.σ_obj, edge, ← Finsupp.single_add]

example : (realizationCoordinates (realizationSimplex repeated sample)).weights 0 = 5 / 6 := by
  rw [repeated_weights]
  norm_num

/-- The operator compatibility also holds for the actual realized point. -/
example : realizationSimplex repeated sample =
    realizationSimplex edge (StdSimplex.map (SimplexCategory.σ (0 : Fin 2)) sample) := by
  exact (realizationSimplex_naturality _ edge sample).symm

/-- An edge distribution with both weights positive. -/
def edgeWeights : StdSimplex ℝ (Fin 2) where
  weights := Finsupp.single 0 (2 / 5) + Finsupp.single 1 (3 / 5)
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Finsupp.sum_add_index]

/-- The ordered two-simplex on zero, one, and two. -/
def ascending : (nerve ℕ) _⦋2⦌ :=
  (show Monotone (fun i : Fin 3 ↦ (i : ℕ)) from fun _ _ h ↦ h).functor

/-- Insert the zero middle coordinate using the actual face operator. -/
def zeroMiddle : StdSimplex ℝ (Fin 3) :=
  StdSimplex.map (SimplexCategory.δ (1 : Fin 3)) edgeWeights

example : zeroMiddle.weights 1 = 0 := by
  norm_num [zeroMiddle, edgeWeights, StdSimplex.weights_map,
    Finsupp.mapDomain_add, Finsupp.mapDomain_single, SimplexCategory.coe_δ]

example : realizationSimplex ascending zeroMiddle =
    realizationSimplex ((nerve ℕ).δ 1 ascending) edgeWeights :=
  realizationSimplex_naturality _ ascending edgeWeights

example : (realizationCoordinates (realizationSimplex ascending zeroMiddle)).weights =
    Finsupp.single 0 (2 / 5) + Finsupp.single 2 (3 / 5) := by
  rw [realizationCoordinates_simplex_weights]
  norm_num [zeroMiddle, edgeWeights, StdSimplex.weights_map,
    Finsupp.mapDomain_add, Finsupp.mapDomain_single, SimplexCategory.coe_δ, ascending]

end QuillenTest.MetricOrderRealization
