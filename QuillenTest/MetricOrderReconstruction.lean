/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.RealizationReconstruction
public import QuillenTest.MetricOrderRealization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Global reconstruction across different original simplex representatives

A degenerate two-simplex with three positive input weights is identified with
an edge carrying the aggregated weights. Reconstruction also respects the
zero-middle-coordinate face of a nondegenerate two-simplex.
-/

@[expose] public section
noncomputable section

open CategoryTheory Convexity Quillen Quillen.MetricOrderComplex
open QuillenTest.MetricOrderRealization
open scoped Simplicial

namespace QuillenTest.MetricOrderReconstruction

/-- The edge weights obtained by merging the first two repeated vertices. -/
def collapsed : StdSimplex ℝ (Fin 2) where
  weights := Finsupp.single 0 (5 / 6) + Finsupp.single 1 (1 / 6)
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Finsupp.sum_add_index]

/-- The coordinate computation on the edge uses the original characteristic map. -/
theorem collapsed_weights :
    (realizationCoordinates (realizationSimplex edge collapsed)).weights =
      Finsupp.single 0 (5 / 6) + Finsupp.single 1 (1 / 6) := by
  rw [realizationCoordinates_simplex_weights]
  norm_num [collapsed, edge, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

/-- Equal aggregate coordinates identify representatives of different dimensions. -/
theorem repeated_eq_collapsed :
    realizationSimplex repeated sample = realizationSimplex edge collapsed := by
  apply realizationCoordinates_injective
  apply MetricOrderComplex.ext
  intro v
  exact congrArg (fun w : ℕ →₀ ℝ ↦ w v) (repeated_weights.trans collapsed_weights.symm)

example : realizationReconstruction (simplexCoordinates edge collapsed) =
    realizationSimplex repeated sample := by
  rw [realizationReconstruction_simplex]
  exact repeated_eq_collapsed.symm

example : realizationReconstruction (simplexCoordinates ascending zeroMiddle) =
    realizationSimplex ((nerve ℕ).δ 1 ascending) edgeWeights := by
  rw [realizationReconstruction_simplex]
  exact realizationSimplex_naturality _ ascending edgeWeights

-- The set equivalence has the exact already-constructed forward map.
example (x : |nerve ℕ|) : realizationCoordinatesEquiv x = realizationCoordinates x := rfl

end QuillenTest.MetricOrderReconstruction
