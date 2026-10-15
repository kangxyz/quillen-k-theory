/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.Waldhausen.QuillenComparison.Equivalence

/-! # Commutativity of the original Quillen K-groups

The genuine canonical Q/S group equivalence transfers the proved Waldhausen
commutativity to exactly the pre-existing Quillen K-group multiplication,
including degree zero. No Grothendieck presentation comparison is used.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
open CategoryTheory Limits
universe u v

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- The original Quillen K-group law is commutative in every degree, including K₀. -/
theorem K_mul_comm (n : ℕ) (a b : E.K n) : a * b = b * a := by
  let e := Waldhausen.QuillenComparison.comparisonKEquiv E n
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  calc
    e x * e y = e (x * y) := (e.map_mul x y).symm
    _ = e (y * x) := congrArg e (Waldhausen.Additivity.K_mul_comm (Waldhausen.ofExactCategory E)
      n x y)
    _ = e y * e x := e.map_mul y x

/-- An explicit commutative-group structure retaining exactly the original
Quillen K-group operations. -/
@[instance_reducible] def KCommGroup (n : ℕ) : CommGroup (E.K n) where
  toGroup := inferInstance
  mul_comm := E.K_mul_comm n

end CategoryTheory.ExactCategory.ExactStructure
