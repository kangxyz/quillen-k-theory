/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.Topology.Homotopy.Basic

/-!
# Pointwise comparison of literal half-time concatenations under two arbitrary functions

Intended upstream module: `Aglib.Topology.Path.HomotopyEvaluationTrans`.

For homotopies on arbitrary topological spaces and two arbitrary functions into a common type,
equality of both evaluated pieces implies equality of their literal half-time concatenations.

Current coefficient-seed and mixed-route consumers: `CoefficientBassPositiveC1SeedFaceNative`.
-/
@[expose] public section
open scoped Topology unitInterval
universe u v w z t
namespace ContinuousMap.Homotopy.Evaluation

/-- Two arbitrary evaluations preserve a common literal concatenation when both pieces match. -/
theorem trans_compare {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z} {T : Type t}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {f g h : C(X, Y)} {f' g' h' : C(X', Y')}
    (H : f.Homotopy g) (K : g.Homotopy h)
    (H' : f'.Homotopy g') (K' : g'.Homotopy h')
    (φ : Y → T) (ψ : Y' → T) (x : X) (x' : X')
    (hH : ∀ s : I, φ (H (s, x)) = ψ (H' (s, x')))
    (hK : ∀ s : I, φ (K (s, x)) = ψ (K' (s, x'))) (s : I) :
    φ ((H.trans K) (s, x)) = ψ ((H'.trans K') (s, x')) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with hs
  · exact hH _
  · exact hK _

end ContinuousMap.Homotopy.Evaluation
