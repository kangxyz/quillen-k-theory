/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian

/-! # Objectwise existence of finite abelian filtrations -/
@[expose] public section

open CategoryTheory.ExactCategory
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- Classical dévissage requires finite filtrations by actual short exact
sequences, starting with a zero object, and with successive quotients in `P`.
No extension closure is required of `P`. -/
def FiltrationHypothesis : Prop :=
  ∀ X : C, Nonempty ((abelianExactStructure C).Filtration P X)

end Quillen.Devissage
