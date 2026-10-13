/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.ExactCategory.Basic
public import Quillen.KTheory.QHomotopy

/-!
# Quillen K-groups of an exact category

For an exact structure `E`, the Q-category uses E's admissible epimorphisms
as left legs and admissible monomorphisms as right legs. All pullback-calculus
instances come from the exact-structure axioms and their proved consequences.
The basepoint is the vertex represented by the zero object of the original
additive category. We make no assertion that it is a zero object in Q.

This file gives the definition, not the K₀ comparison theorem or the deeper
structural theorems of algebraic K-theory.
-/
@[expose] public section


noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen
namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The Quillen Q-category attached to the given exact structure. -/
abbrev QCategory := Quillen.Q E.deflation E.inflation

/-- Quillen's classifying space, the geometric realization of the Q-category's nerve. -/
abbrev KSpace := Quillen.ClassifyingSpace E.QCategory

/-- The basepoint supplied by the original category's zero object. -/
def kBasepoint : E.KSpace :=
  Quillen.classifyingSpacePoint (Quillen.Q.of E.deflation E.inflation (0 : C))

/-- The nonnegative Quillen K-group, defined by the shifted homotopy group
`π_(n+1)(|NQ(E)|, 0)`. -/
abbrev K (n : ℕ) :=
  Quillen.QHomotopyGroup E.deflation E.inflation (0 : C) n

/-- In every degree the construction inherits a group structure. -/
example (n : ℕ) : Group (E.K n) := inferInstance

/-- In strictly positive K-degree the group is commutative by higher homotopy
commutativity. K₀ commutativity requires a separate Q-specific theorem. -/
example (n : ℕ) : CommGroup (E.K (n + 1)) := inferInstance

end ExactStructure
end Quillen
