/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Algebra.Matrix.RightAutomorphisms
import Mathlib.Algebra.Ring.PUnit

/-! Regression tests for concrete right-module automorphisms and actual biproduct stabilization. -/

open CategoryTheory CategoryTheory.Limits Quillen
open Quillen.RightMatrix

universe u
variable {R : Type u} [Ring R]

example (n : ℕ) (g : StableGeneralLinear.GL R n) (x : Fin (n + 1) → Rᵐᵒᵖ) :
    (moduleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x (Fin.last n) =
      x (Fin.last n) := moduleAutEquiv_step_last R n g x

example (n : ℕ) (g : StableGeneralLinear.GL R n) :
    moduleAutEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (appendIso R n).symm ≪≫
        biprod.mapIso (moduleAutEquiv R n g) (Iso.refl (freeModule R 1)) ≪≫ appendIso R n :=
  moduleAutEquiv_step R n g

example (n : ℕ) (a : Aut (FiniteProjectiveModule.free (R := Rᵐᵒᵖ) n)) :
    ∃ g : StableGeneralLinear.GL R n, freeAutEquiv R n g = a :=
  (freeAutEquiv R n).surjective a

-- Zero rings remain valid, with no assumption that distinct ranks are nonisomorphic.
example (n : ℕ) (a : Aut (freeModule PUnit n)) : moduleAutEquiv PUnit n
    ((moduleAutEquiv PUnit n).symm a) = a := (moduleAutEquiv PUnit n).apply_symm_apply a

-- Noncommutative matrix coefficient rings retain the same concrete stabilization law.
example (g : StableGeneralLinear.GL (Matrix (Fin 2) (Fin 2) ℤ) 1) :
    (moduleAutEquiv _ 2 (StableGeneralLinear.step _ 1 g)).hom ≫ (appendIso _ 1).inv =
      (appendIso _ 1).inv ≫ biprod.map (moduleAutEquiv _ 1 g).hom (𝟙 (freeModule _ 1)) :=
  moduleAutEquiv_stabilization _ 1 g
