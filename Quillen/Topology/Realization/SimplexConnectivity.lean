/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Connectivity of the actual finite standard simplex

The finitely supported standard simplex embeds in its finite coordinate space
with convex image. Its genuine homeomorphism onto this image proves
contractibility and local path connectedness. These are properties of the
actual simplex used to parametrize singular simplices, rather than hypotheses
on a substitute model.
-/

@[expose] public section

noncomputable section

open Convexity

namespace Quillen

/-- The coordinate image of the standard simplex is convex. -/
theorem convex_stdSimplex_coordinateRange (M : Type*) :
    Convex ℝ (Set.range (fun x : StdSimplex ℝ M ↦ (x.weights : M → ℝ))) := by
  rintro x ⟨x, rfl⟩ y ⟨y, rfl⟩ a b ha hb hab
  refine ⟨convexCombPair a b ha hb hab x y, ?_⟩
  ext i
  simp [StdSimplex.weights_convexCombPair]

/-- Every nonempty finite standard simplex is contractible. -/
theorem contractibleSpace_stdSimplex (M : Type*) [Finite M] [Nonempty M] :
    ContractibleSpace (StdSimplex ℝ M) := by
  let := (convex_stdSimplex_coordinateRange M).contractibleSpace
    (Set.range_nonempty (fun x : StdSimplex ℝ M ↦ (x.weights : M → ℝ)))
  exact (StdSimplex.isEmbedding_toFun_comp_weights ℝ M).toHomeomorph.contractibleSpace

/-- Every finite standard simplex is locally path connected, including the empty one. -/
theorem locallyPathConnectedSpace_stdSimplex (M : Type*) [Finite M] :
    LocallyPathConnectedSpace (StdSimplex ℝ M) := by
  let := (convex_stdSimplex_coordinateRange M).locallyPathConnectedSpace
  exact (StdSimplex.isEmbedding_toFun_comp_weights ℝ M).toHomeomorph.symm.locallyPathConnectedSpace

/-- The actual finite nonempty simplex is simply connected. -/
theorem simplyConnectedSpace_stdSimplex (M : Type*) [Finite M] [Nonempty M] :
    SimplyConnectedSpace (StdSimplex ℝ M) := by
  let := contractibleSpace_stdSimplex M
  infer_instance

end Quillen
