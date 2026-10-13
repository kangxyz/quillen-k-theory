/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.Reconstruction

/-!
# Independent consumers of actual realization coordinates

For an arbitrary poset universe, the original classifying space admits a
surjective continuous map to its L1 coordinate model. This client reconstructs
points on exact positive support and uses injectivity on nondegenerate charts.
The final example uses the uncountable inclusion poset of sets of real numbers.
-/

@[expose] public section
noncomputable section

open CategoryTheory Convexity Quillen Quillen.MetricOrderComplex
open scoped Simplicial

universe u

namespace Consumer.MetricOrderRealization

/-- Equal metric coordinates on a fixed nondegenerate simplex recover all input weights. -/
theorem recover_weights {P : Type u} [PartialOrder P] {n : ℕ}
    (s : (nerve P) _⦋n⦌) (hs : s ∈ (nerve P).nonDegenerate n)
    (t q : StdSimplex ℝ (Fin (n + 1)))
    (h : realizationCoordinates (realizationSimplex s t) =
      realizationCoordinates (realizationSimplex s q)) : t = q := by
  rw [realizationCoordinates_simplex, realizationCoordinates_simplex] at h
  exact chainCoordinates_injective s.obj s.monotone.isChain_range
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs).injective h

/-- An arbitrary coordinate can be read continuously from the original realization. -/
theorem continuous_original_weight {P : Type u} [PartialOrder P] (p : P) :
    Continuous (fun z : |nerve P| ↦ (realizationCoordinates z).weights p) :=
  (continuous_coordinate p).comp realizationCoordinates.continuous

/-- The source simplex for a distribution has exactly its ordered, positive support. -/
example (x : MetricOrderComplex (Set ℝ)) :
    ∃ (n : ℕ) (s : (nerve (Set ℝ)) _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))),
      s ∈ (nerve (Set ℝ)).nonDegenerate n ∧
      Set.range s.obj = (x.weights.support : Set (Set ℝ)) ∧
      (∀ i, 0 < t.weights i) ∧
      realizationCoordinates (realizationSimplex s t) = x :=
  exists_nondegenerate_representation x

example (A : Set ℝ) : realizationCoordinates (classifyingSpacePoint.{0, 0} A) = vertex A :=
  realizationCoordinates_vertex A

end Consumer.MetricOrderRealization
