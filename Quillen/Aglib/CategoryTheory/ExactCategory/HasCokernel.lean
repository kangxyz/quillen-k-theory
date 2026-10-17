/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Aglib.CategoryTheory.ExactCategory.Basic

/-!
# Actual cokernels of admissible monomorphisms

The original defining conflation supplies the genuine cokernel universal
property of every admissible monomorphism, without an ambient abelian category.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- An inflation has an actual cokernel, supplied by its defining conflation. -/
theorem hasCokernel_of_inflation {X Y : C} (f : X ⟶ Y) (hf : E.inflation f) : HasCokernel f := by
  obtain ⟨Z, p, w, h⟩ := hf
  exact ⟨⟨CokernelCofork.ofπ p w, E.cokernel _ h⟩⟩

end Quillen.Waldhausen.QuillenComparison
