/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.Homotopy

/-!
# Explicit relative path homotopies inside finite simplices

Pointwise convex interpolation is jointly continuous for finite standard
simplices. Thus two paths with the same endpoints are homotopic relative
to their endpoints. This supplies the topological filling needed to realize
simplicial two-simplex composition relations.
-/
@[expose] public section


noncomputable section

open CategoryTheory Opposite Convexity
open scoped Simplicial Topology unitInterval

universe u

namespace Quillen

/-- Jointly continuous convex interpolation of two moving points in a finite simplex. -/
def stdSimplexPathHomotopy {M : Type*} [Finite M]
    {x y : StdSimplex ℝ M} (p q : Path x y) : p.Homotopy q where
  toFun z := convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (p z.2) (q z.2)
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
    unfold Function.comp
    refine continuous_pi (fun i ↦ ?_)
    simp only [unitInterval.coe_symm_eq, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' t z hz := by
    rcases hz with hz | hz
    · subst z
      simp
    · rw [Set.mem_singleton_iff] at hz
      subst z
      simp

/-- Any two paths in a finite topological standard simplex with fixed
endpoints are homotopic relative to the endpoints. -/
theorem stdSimplex_paths_homotopic {M : Type*} [Finite M]
    {x y : StdSimplex ℝ M} (p q : Path x y) : p.Homotopic q :=
  ⟨stdSimplexPathHomotopy p q⟩

end Quillen
