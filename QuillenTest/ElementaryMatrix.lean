/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Aglib.LinearAlgebra.Matrix.Elementary

/-! Regression tests for noncommutative elementary matrix identities. -/

open Quillen.ElementaryMatrix
open scoped commutatorElement

variable {R : Type*} [Ring R]

example (a b : R) :
    ⁅unit (0 : Fin 3) 1 (by decide) a, unit (1 : Fin 3) 2 (by decide) b⁆ =
      unit (0 : Fin 3) 2 (by decide) (a * b) :=
  unit_commutator 0 1 2 (by decide) (by decide) (by decide) a b

example : Group.IsPerfect (subgroup (Fin 3) R) :=
  subgroup_isPerfect (by decide)

example : Group.IsPerfect (subgroup (Fin 0) R) :=
  subgroup_isPerfect (by decide)

-- A genuinely noncommutative coefficient ring is permitted.
example : Group.IsPerfect (subgroup (Fin 3) (Matrix (Fin 2) (Fin 2) ℤ)) :=
  subgroup_isPerfect (by decide)

example {S : Type*} [Ring S] (f : R →+* S) (a : R) :
    map f (unit (0 : Fin 2) 1 (by decide) a) ∈ subgroup (Fin 2) S := by
  rw [map_unit]
  exact unit_mem_subgroup 0 1 (by decide) (f a)
