/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Aglib.CategoryTheory.ExactCategory.Basic
import Quillen.CategoryTheory.ExactCategory.ExtensionProjectionFunctor
import Quillen.Algebra.Category.ModuleCat.FiniteProjective

open CategoryTheory.ExactCategory


/-! # The actual extension projection and its original Q functor laws -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

example : E.ExtensionTotal ⥤ Q E.deflation E.inflation := E.extensionProjection

example {x y z : E.ExtensionTotal} (f : x ⟶ y) (g : y ⟶ z) :
    E.extensionProjectionQMap (f ≫ g) =
      E.extensionProjectionQMap f ≫ E.extensionProjectionQMap g :=
  E.extensionProjectionQMap_comp f g

example (R : Type u) [Ring R] :
    (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).ExtensionTotal ⥤
      Q (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).deflation
        (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).inflation :=
  (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).extensionProjection
