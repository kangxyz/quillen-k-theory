/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.QConstruction.Basic
public import Quillen.Topology.ClassifyingSpace.Basic

/-!
# The homotopy groups of the restricted-span classifying space

This combines two genuine constructions: the category of spans modulo
isomorphism, and the geometric realization of its nerve. It is a generic
construction on a restricted-span calculus with a chosen object. The exact
category specialization in `Quillen.KTheory` obtains the hypotheses from the
proved exact-structure interface.
-/
@[expose] public section


noncomputable section

universe v u

open CategoryTheory

namespace Quillen

variable {C : Type u} [Category.{v} C]
  (deflation inflation : MorphismProperty C)
  [deflation.ContainsIdentities] [inflation.ContainsIdentities]
  [deflation.IsStableUnderComposition] [inflation.IsStableUnderComposition]
  [deflation.HasPullbacksAgainst inflation]
  [deflation.IsStableUnderBaseChangeAgainst inflation]
  [inflation.IsStableUnderBaseChangeAgainst deflation]

/-- The actual realization of the nerve of the restricted-span category. -/
abbrev QClassifyingSpace := ClassifyingSpace (Q deflation inflation)

/-- The shifted homotopy group at the distinguished object `zero`.
No claim that `zero` is a zero object in the Q-category is made or needed. -/
abbrev QHomotopyGroup (zero : C) (n : ℕ) :=
  ShiftedHomotopyGroup (Q deflation inflation) (Q.of deflation inflation zero) n

/-- Group structure in every nonnegative K-style degree. -/
example (zero : C) (n : ℕ) : Group (QHomotopyGroup deflation inflation zero n) :=
  inferInstance

/-- Commutativity in positive K-style degree, from higher homotopy groups. -/
example (zero : C) (n : ℕ) : CommGroup (QHomotopyGroup deflation inflation zero (n + 1)) :=
  inferInstance

end Quillen
