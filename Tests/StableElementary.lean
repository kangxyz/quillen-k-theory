/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.Algebra.Group.StableElementary
import Mathlib.Algebra.Ring.PUnit

/-! Actual stable elementary groups, including noncommutative and zero coefficient rings. -/

open Quillen.StableGeneralLinear
open scoped commutatorElement

variable {R : Type*} [Ring R]

example : _root_.Group.IsPerfect (elementary R) := inferInstance

example : (elementary R).Normal := inferInstance

example : elementary R = commutator (Quillen.StableGeneralLinear.Group R) :=
  elementary_eq_commutator R

example (g h : Quillen.StableGeneralLinear.Group R) : ⁅g, h⁆ ∈ elementary R := by
  apply commutator_le_elementary R
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)

example : elementary (Matrix (Fin 2) (Fin 2) ℤ) =
    commutator (Quillen.StableGeneralLinear.Group (Matrix (Fin 2) (Fin 2) ℤ)) :=
  elementary_eq_commutator _

example : _root_.Group.IsPerfect (elementary PUnit) := inferInstance

example (g : Quillen.StableGeneralLinear.Group PUnit) : g = 1 := by
  obtain ⟨n, a, rfl⟩ := exists_of PUnit g
  have ha : a = 1 := Subsingleton.elim _ _
  rw [ha, map_one]

example {S : Type*} [Ring S] (f : R →+* S) (g : Quillen.StableGeneralLinear.Group R)
    (hg : g ∈ elementary R) :
    map f g ∈ elementary S :=
  map_elementary_le f (Subgroup.mem_map_of_mem _ hg)

example (H : Subgroup (Quillen.StableGeneralLinear.Group R)) [_root_.Group.IsPerfect H] :
    H ≤ elementary R :=
  perfect_le_elementary R H
