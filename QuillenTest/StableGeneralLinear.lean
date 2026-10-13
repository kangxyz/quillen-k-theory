/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Algebra.Group.StableGeneralLinear
import Mathlib.Algebra.Ring.PUnit

/-! Regression tests for stabilization, finite representatives, and change of rings. -/

open Quillen.StableGeneralLinear

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

example (g : GL R 0) : of R 0 g = 1 := by
  have : g = 1 := Subsingleton.elim _ _
  simp [this]

example (g : GL R 2) : of R 3 (step R 2 g) = of R 2 g := by
  rw [← transition_succ, of_transition]

example {n m : ℕ} (h : n ≤ m) (a b : GL R n)
    (e : transition R n m h a = transition R n m h b) : a = b :=
  transition_injective R n m h e

example (x y : Quillen.StableGeneralLinear.Group R) :
    ∃ n, ∃ a b : GL R n, x * y = of R n (a * b) := by
  obtain ⟨n, a, b, rfl, rfl⟩ := exists_of₂ R x y
  exact ⟨n, a, b, (map_mul (of R n) a b).symm⟩

example (f : R →+* S) (g : S →+* T) (n : ℕ) (a : GL R n) :
    map g (map f (of R n a)) = map (g.comp f) (of R n a) := by
  rw [map_comp]
  rfl

-- Matrix coefficients need not commute, even when the underlying scalar ring does.
example (g : GL (Matrix (Fin 2) (Fin 2) ℤ) 2) :
    (step _ 2 g).val (Fin.last 2) (Fin.last 2) = 1 :=
  step_val_last _ _ _

-- The zero ring is allowed; no invariant basis number hypothesis is present.
example (x y : Quillen.StableGeneralLinear.Group PUnit) : x = y := by
  obtain ⟨n, a, b, rfl, rfl⟩ := exists_of₂ PUnit x y
  exact congrArg (of PUnit n) (Subsingleton.elim a b)

example (x : Fin 4 → Quillen.StableGeneralLinear.Group R) :
    ∃ n, ∃ a : Fin 4 → GL R n, ∀ i, x i = of R n (a i) := exists_of_family R x
