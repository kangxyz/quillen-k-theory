/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.CategoryTheory.ExactCategory.ExtensionSpanLift

/-! # Actual original-Q lifting without any splitting or abelian hypothesis -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

example {X : C} (y : E.ExtensionTotal)
    (s : Span E.deflation E.inflation X (E.extensionProjectionObject y)) :
    E.ExtensionSpanLift y s := E.extensionSpanLift y s

example {X : C} (y : E.ExtensionTotal)
    (g : Quillen.Q.of E.deflation E.inflation X ⟶ E.extensionProjectionQObj y) :
    ∃ (x : E.ExtensionTotal) (e : (E.extensionQuotientData x).obj ≅ X) (f : x ⟶ y),
      E.extensionProjectionQMap f = (E.qIsoOfIso e).hom ≫ g :=
  E.exists_extensionLift y g
