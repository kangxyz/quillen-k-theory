/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.Topology.Homotopy.Path

/-!
# Pointwise homotopy slices preserve the literal path concatenation and reversal clocks

Intended upstream module: `Aglib.Topology.Path.HomotopyPathSlice`.

For arbitrary topological spaces, a homotopy slice, and an arbitrary evaluation function, the
stated equalities at every slice time preserve literal path concatenation and reversal.

Current coefficient-seed and mixed-route consumers: `CoefficientBassPositiveC1WholeOldSeedSeam`,
`CoefficientBassPositiveJ0C0SeedSeam`.
-/
@[expose] public section
set_option autoImplicit false
open scoped Topology unitInterval
namespace ContinuousMap.Homotopy.PathSlice
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f g h : C(X, Y)} {a b c : Z}

/-- Whole slice equalities preserve the original half-time concatenation. -/
theorem trans (F : f.Homotopy g) (G : g.Homotopy h) (φ : Y → Z) (x : X)
    (γ : Path a b) (δ : Path b c)
    (hF : ∀ s, φ (F (s, x)) = γ s) (hG : ∀ s, φ (G (s, x)) = δ s) (s : I) :
    φ ((F.trans G) (s, x)) = (γ.trans δ) s := by
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

/-- Whole slice equality preserves reversal at the same interval coordinate. -/
theorem symm (F : f.Homotopy g) (φ : Y → Z) (x : X) (γ : Path a b)
    (hF : ∀ s, φ (F (s, x)) = γ s) (s : I) :
    φ (F.symm (s, x)) = γ.symm s :=
  hF (unitInterval.symm s)

end ContinuousMap.Homotopy.PathSlice
