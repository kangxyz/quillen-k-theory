/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyFiber.CartesianTransport

/-! Regression tests for the original homotopy-fiber map of a weakly
cartesian square, including arbitrary base maps, full paths, and degree zero. -/
@[expose] public section


noncomputable section
open Quillen
open scoped Topology unitInterval
universe u

variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X,A)} {q : C(Y,B)} (u : C(X,Y)) (v : C(A,B))
  (sq : v.comp p = q.comp u)
  (h : IsWeakHomotopyEquivalence (HomotopyPullback.comparison q v p u sq.symm))
  (a : A)

-- Weak cartesianness gives all homotopy-group bijections for the actual map,
-- with no requirement that v itself be weak.
example (z : HomotopyFiber p a) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (HomotopyFiber.map u v sq a) (x := z) rfl) :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence_of_comparison u v sq h a).homotopy_bijective z n

example [IsEmpty (HomotopyFiber p a)] : IsEmpty (HomotopyFiber q (v a)) :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence_of_comparison u v sq h a).isEmpty_target

-- The induced map retains the original source coordinate and every value
-- of the postcomposed path, not merely its endpoints or homotopy class.
example (z : HomotopyFiber p a) :
    (HomotopyFiber.map u v sq a z).val.1 = u z.val.1 ∧
      ∀ t, (HomotopyFiber.map u v sq a z).val.2 t = v (z.val.2 t) :=
  ⟨rfl, fun _ ↦ rfl⟩

example (z : HomotopyFiber p a) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (HomotopyFiber.map u v sq a) (x := z) rfl) :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence_of_comparison u v sq h a).homotopy_bijective z 0
