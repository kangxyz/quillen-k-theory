/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.CommonPoint
public import Quillen.Topology.MetricOrderComplex.SimplexCoordinates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Common points without a chain union

Two edges in the inclusion poset of subsets of Bool share the empty-set vertex,
but their other vertices are incomparable. Their half-half distributions have
positive common mass and normalized common point equal to the shared vertex.
The union of their supports is explicitly not a chain.
-/

@[expose] public section
noncomputable section

open CategoryTheory Convexity Quillen Quillen.MetricOrderComplex
open scoped Simplicial

namespace QuillenTest.MetricOrderCommonPoint

/-- Equal barycentric weights at the ends of an edge. -/
def halves : StdSimplex ℝ (Fin 2) where
  weights := Finsupp.single 0 (1 / 2) + Finsupp.single 1 (1 / 2)
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Finsupp.sum_add_index]

/-- Each branch runs from the empty set to one of two incomparable singletons. -/
def branch (b : Bool) : (nerve (Set Bool)) _⦋1⦌ :=
  (show Monotone (fun i : Fin 2 ↦ if i = 0 then (∅ : Set Bool) else {b}) from by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all).functor

/-- The actual half-half coordinate distribution on a branch. -/
def branchPoint (b : Bool) : MetricOrderComplex (Set Bool) := simplexCoordinates (branch b) halves

/-- Both support vertices carry positive weight. -/
theorem branchPoint_weights (b : Bool) :
    (branchPoint b).weights = Finsupp.single ∅ (1 / 2) + Finsupp.single {b} (1 / 2) := by
  change (simplexCoordinates (branch b) halves).weights = _
  rw [simplexCoordinates_weights]
  norm_num [halves, Finsupp.mapDomain_add, Finsupp.mapDomain_single, branch]

/-- Common mass remains positive even though the support union is not a simplex. -/
theorem fork_commonMass : commonMass (branchPoint false) (branchPoint true) = 1 / 2 := by
  have hw : commonWeights (branchPoint false) (branchPoint true) =
      Finsupp.single ∅ (1 / 2 : ℝ) := by
    ext v
    simp only [commonWeights_apply, branchPoint_weights, Finsupp.add_apply]
    by_cases h0 : v = ∅
    · subst v; norm_num
    by_cases hf : v = ({false} : Set Bool)
    · subst v; norm_num
    by_cases ht : v = ({true} : Set Bool)
    · subst v; norm_num
    simp [h0, hf, ht]
  simp [commonMass, hw]

/-- The resulting common point is exactly the shared original vertex. -/
theorem fork_commonPoint :
    commonPoint (branchPoint false) (branchPoint true) (by rw [fork_commonMass]; norm_num) =
      vertex (∅ : Set Bool) := by
  ext v
  rw [commonPoint_weights, branchPoint_weights, branchPoint_weights, fork_commonMass]
  by_cases h0 : v = ∅
  · subst v; norm_num
  by_cases hf : v = ({false} : Set Bool)
  · subst v; norm_num
  by_cases ht : v = ({true} : Set Bool)
  · subst v; norm_num
  simp [h0, hf, ht]

/-- The two outer support vertices are incomparable, so a direct affine union is invalid. -/
theorem fork_support_union_not_chain :
    ¬IsChain (· ≤ ·) (((branchPoint false).weights.support ∪
      (branchPoint true).weights.support : Finset (Set Bool)) : Set (Set Bool)) := by
  intro h
  have hf : ({false} : Set Bool) ∈ ((branchPoint false).weights.support ∪
      (branchPoint true).weights.support : Finset (Set Bool)) := by
    simp [branchPoint_weights]
  have ht : ({true} : Set Bool) ∈ ((branchPoint false).weights.support ∪
      (branchPoint true).weights.support : Finset (Set Bool)) := by
    simp [branchPoint_weights]
  have hc := h hf ht (by simp : ({false} : Set Bool) ≠ {true})
  simp at hc

/-- The genuine L1 distance detects exactly the half-unit common mass. -/
theorem fork_dist : dist (branchPoint false) (branchPoint true) = 1 := by
  have h := twice_commonMass_add_dist (branchPoint false) (branchPoint true)
  rw [fork_commonMass] at h
  linarith

end QuillenTest.MetricOrderCommonPoint
