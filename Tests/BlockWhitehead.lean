/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.Algebra.Matrix.BlockWhitehead

/-! Whitehead factorizations must apply to arbitrary, not just elementary, units. -/

open Quillen.ElementaryMatrix
open scoped commutatorElement

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

example (g : (Matrix n n R)ˣ) : blockSum g g⁻¹ ∈ subgroup (n ⊕ n) R :=
  blockSum_inv_mem_subgroup g

example (g h : (Matrix n n R)ˣ) :
    blockSum ⁅g, h⁆ (1 : (Matrix n n R)ˣ) ∈ subgroup (n ⊕ n) R :=
  blockSum_commutator_mem_subgroup g h

example (g h : (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ))ˣ) :
    blockSum ⁅g, h⁆ (1 : (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ))ˣ) ∈
      subgroup (Fin 2 ⊕ Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) :=
  blockSum_commutator_mem_subgroup g h

example (a : R) :
    blockSum (unit (0 : Fin 2) 1 (by decide) a) (1 : (Matrix (Fin 0) (Fin 0) R)ˣ) =
      unit (Sum.inl 0 : Fin 2 ⊕ Fin 0) (Sum.inl 1) (by decide) a :=
  blockSum_unit_one 0 1 (by decide) a
