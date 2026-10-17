/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Module.RightScalarExtension

/-!
# Arbitrarily universed balanced tensor consumers

The additive universal property is tested with an abelian target carrying no
scalar action. Separate ring, source-module, and target-module universes test
the semilinear adjunction. The final calculation retains the order of three
coefficients over arbitrary, potentially noncommutative rings.
-/

@[expose] public section

noncomputable section

universe u v w z a b

open Quillen.RightScalarExtension MulOpposite

namespace BalancedRightTensorConsumer

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M]

example {A : Type z} [AddCommGroup A] (f : R →+* S) (h : M →+ S →+ A)
    (hb : ∀ r m s, h (op r • m) s = h m (f r * s)) :
    ∃! H : Tensor f M →+ A, ∀ m s, H (pure f m s) = h m s := by
  refine ⟨liftAddHom f ⟨h, hb⟩, fun _ _ => rfl, ?_⟩
  intro H hH
  exact liftAddHom_unique f ⟨h, hb⟩ H hH

example {N : Type z} [AddCommGroup N] [Module Sᵐᵒᵖ N]
    (f : R →+* S) (h : M →ₛₗ[f.op] N) :
    ∃! H : Tensor f M →ₗ[Sᵐᵒᵖ] N, ∀ m, H (unit f m) = h m := by
  refine ⟨lift f h, lift_unit f h, ?_⟩
  intro H hH
  exact lift_unique f h H hH

example {N : Type z} [AddCommGroup N] [Module Sᵐᵒᵖ N]
    (f : R →+* S) (h : M →ₛₗ[f.op] N) (m : M) (r : R) (s t : S) :
    lift f h (op t • pure f (op r • m) s) = op (f r * s * t) • h m := by
  rw [pure_balance, pure_smul, lift_pure]

example {T : Type a} [Ring T] {Q : Type b} [AddCommGroup Q] [Module Tᵐᵒᵖ Q]
    (f : R →+* S) (g : S →+* T) (h : M →ₛₗ[(g.comp f).op] Q) :
    ∃! H : Tensor f M →ₛₗ[g.op] Q, ∀ m, H (unit f m) = h m := by
  refine ⟨liftSemilinear f g h, liftSemilinear_unit f g h, ?_⟩
  intro H hH
  exact liftSemilinear_unique f g h H hH

end BalancedRightTensorConsumer
