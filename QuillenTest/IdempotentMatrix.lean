/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Aglib.Algebra.Category.ModuleCat.IdempotentMatrix
import Mathlib.Algebra.Ring.PUnit

/-! Right-module matrix action and actual projective images work over arbitrary rings. -/

open Quillen.RightMatrix

noncomputable section

universe u

variable {R : Type u} [Ring R]

example {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (r : R) :
    linearMap A (MulOpposite.op r • x) = MulOpposite.op r • linearMap A x :=
  map_smul (linearMap A) _ _

example {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : A * A = A) :
    (linearMap A).rangeRestrict.comp (linearMap A).range.subtype = LinearMap.id :=
  rangeRestrict_comp_subtype A hA

example {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : A * A = A) :
    Module.Projective Rᵐᵒᵖ (linearMap A).range := image_projective A hA

example (M : ModuleCat.{u} Rᵐᵒᵖ) [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
      A * A = A ∧ Nonempty (M ≃ₗ[Rᵐᵒᵖ] (linearMap A).range) :=
  exists_idempotent_image M

example : Module.Projective (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
    (linearMap (1 : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) ℤ))).range :=
  image_projective _ (one_mul _)

example : Module.Projective PUnitᵐᵒᵖ
    (linearMap (1 : Matrix (Fin 0) (Fin 0) PUnit)).range :=
  image_projective _ (one_mul _)

example {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    endRingEquiv (A * B) = endRingEquiv A * endRingEquiv B :=
  map_mul endRingEquiv A B
