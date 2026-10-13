/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.LinearAlgebra.Prod

/-! # Signed maps from a Cartesian product

Postcomposition transports the original difference of two linear maps.
-/

@[expose] public section

section

universe u v w x y
namespace LinearMap
variable {R : Type u} [Ring R]
variable {A : Type v} {B : Type w} {C : Type x} {D : Type y}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable [Module R A] [Module R B] [Module R C] [Module R D]
/-- Postcomposition preserves a signed pair map when it preserves both components. -/
theorem postcompose_pairDifference (p : A →ₗ[R] C) (q : B →ₗ[R] C)
    (s : C →ₗ[R] D) (p' : A →ₗ[R] D) (q' : B →ₗ[R] D)
    (hp : s.comp p = p') (hq : s.comp q = q') :
    s.comp (p.comp (fst R A B) - q.comp (snd R A B)) =
      p'.comp (fst R A B) - q'.comp (snd R A B) := by
  rw [comp_sub, ← comp_assoc, ← comp_assoc, hp, hq]
end LinearMap

end
