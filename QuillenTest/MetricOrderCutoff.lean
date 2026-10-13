/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.CutoffHomotopy
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A nontrivial cutoff in the three-vertex order simplex

The distribution `(1/2, 1/3, 1/6)` is sent to `(3/4, 1/4, 0)`.
Thus this test checks actual normalization and deletion of a positive input
coordinate, rather than merely naming the abstract API.
-/

@[expose] public section

open Quillen Quillen.MetricOrderComplex
open scoped unitInterval

namespace QuillenTest.MetricOrderCutoff

noncomputable def sample : MetricOrderComplex (Fin 3) := by
  refine ⟨⟨Finsupp.single 0 (1 / 2) + Finsupp.single 1 (1 / 3) +
    Finsupp.single 2 (1 / 6), ?_, ?_⟩, ?_⟩
  · intro v
    fin_cases v <;> norm_num
  · norm_num [Finsupp.sum_add_index]
  · intro a _ b _ _
    exact le_total a b

theorem sample_maximum : sample.maximum = 1 / 2 := by
  apply le_antisymm
  · apply maximum_le
    intro v
    fin_cases v <;> norm_num [sample, weights]
  · simpa [sample, weights] using sample.weight_le_maximum 0

theorem sample_cutoffWeights : sample.cutoffWeights =
    Finsupp.single 0 (1 / 4) + Finsupp.single 1 (1 / 12) := by
  ext v
  simp only [cutoffWeights_apply, sample_maximum]
  fin_cases v <;> norm_num [sample, weights]

theorem sample_cutoffMass : sample.cutoffMass = 1 / 3 := by
  norm_num [cutoffMass, sample_cutoffWeights, Finsupp.sum_add_index]

example : sample.cutoff.weights 0 = 3 / 4 := by
  rw [cutoff_weights_apply, sample_cutoffMass, sample_maximum]
  norm_num [sample, weights]

example : sample.cutoff.weights 1 = 1 / 4 := by
  rw [cutoff_weights_apply, sample_cutoffMass, sample_maximum]
  norm_num [sample, weights]

theorem sample_cutoff_two : sample.cutoff.weights 2 = 0 := by
  rw [cutoff_weights_apply, sample_cutoffMass, sample_maximum]
  norm_num [sample, weights]

example : sample.weights 2 > 0 := by norm_num [sample, weights]

example (y : MetricOrderComplex (Fin 3)) (hy : dist y sample < 1 / 8) :
    y.cutoff.weights.support ⊆ sample.weights.support := by
  apply cutoff_support_subset_of_dist_lt
  norm_num [sample_maximum]
  exact hy

-- At the midpoint, a coordinate deleted by cutoff is already restored halfway.
example : (cutoffHomotopy ((⟨1 / 2, by constructor <;> norm_num⟩ : I), sample)).weights 2 =
    1 / 12 := by
  change (cutoffBlend _ sample).weights 2 = _
  rw [cutoffBlend_weights, sample_cutoff_two]
  norm_num [sample, weights]

end QuillenTest.MetricOrderCutoff
