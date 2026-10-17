/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Aglib.LinearAlgebra.Matrix.RightAutomorphismsLeft

/-! Regression tests for explicit basis reversal and the actual left free sequence. -/

open CategoryTheory CategoryTheory.Limits Quillen Quillen.RightMatrix
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

universe u
variable {R : Type u} [Ring R]

example (n : ℕ) (x : Fin n → Rᵐᵒᵖ) :
    reverseColumns R n (reverseColumns R n x) = x := by
  ext i
  exact congrArg x (Fin.rev_rev i)

example (n : ℕ) (g : StableGeneralLinear.GL R n) :
    leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (FiniteProjectiveModule.freeSuccIso (R := Rᵐᵒᵖ) n).symm ≪≫
        biprod.mapIso (Iso.refl _) (leftFreeAutEquiv R n g) ≪≫
          FiniteProjectiveModule.freeSuccIso n := leftFreeAutEquiv_step R n g

example (g : StableGeneralLinear.GL (Matrix (Fin 2) (Fin 2) ℤ) 2)
    (x : Fin 3 → (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ) :
    (leftModuleAutEquiv _ 3 (StableGeneralLinear.step _ 2 g)).hom x 0 = x 0 :=
  leftModuleAutEquiv_step_zero _ 2 g x
