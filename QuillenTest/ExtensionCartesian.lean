/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.CategoryTheory.ExactCategory.ExtensionCartesianPredicate

/-! # Genuine cartesian uniqueness for the original extension projection -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

example {x y z : E.ExtensionTotal} (f : x ⟶ z) (g : y ⟶ z)
    (w : E.extensionProjectionQObj y ⟶ E.extensionProjectionQObj x)
    (hw : E.extensionProjectionQMap g = w ≫ E.extensionProjectionQMap f) :
    ∃! h : y ⟶ x, E.extensionProjectionQMap h = w ∧ h ≫ f = g :=
  E.existsUnique_extensionFactor f g w hw

example : E.extensionTotalMiddle.Faithful := inferInstance
example {x y : E.ExtensionTotal} (f : x ⟶ y) : Mono f := inferInstance

example {x y : E.ExtensionTotal} (f : x ⟶ y) :
    E.extensionProjection.IsStronglyCartesian (E.extensionProjection.map f) f := inferInstance
