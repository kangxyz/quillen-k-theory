/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyFiber.Basic

/-!
# Separation of original path-space homotopy fibers

The original fiber is a subspace of the product of the source with a compact-open path space.
T1 separation of source and target therefore gives T1 separation of this unchanged fiber.
-/

@[expose] public section

open scoped unitInterval

universe u v

namespace Quillen.HomotopyFiber

/-- T1 separation is inherited by the original path-space fiber, with no closedness assumption. -/
instance t1Space {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y] (f : C(X, Y)) (y : Y) : T1Space (HomotopyFiber f y) := by
  let : T1Space C(unitInterval, Y) :=
    t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun
  exact inferInstanceAs (T1Space {z : X × C(unitInterval, Y) // z.2 0 = f z.1 ∧ z.2 1 = y})

end Quillen.HomotopyFiber
