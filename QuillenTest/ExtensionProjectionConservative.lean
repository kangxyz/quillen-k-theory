/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.CategoryTheory.ExactCategory.ExtensionProjectionConservative

/-! # Conservativity of the actual unlocalized extension projection -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

example : E.extensionProjection.ReflectsIsomorphisms := inferInstance

example {x y : E.ExtensionTotal} (f : x ⟶ y) [IsIso (E.extensionProjectionQMap f)] :
    IsIso f := E.extensionProjection_isIso f
