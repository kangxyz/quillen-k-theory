/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.CategoryTheory.ExactCategory.ExtensionProjection

/-! # The quotient-span assignment lands in the original Q category -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

example {x y : E.ExtensionTotal} (f : x ⟶ y) :
    E.deflation (E.extensionProjectionSpan f).l := (E.extensionProjectionSpan f).wl

example {x y : E.ExtensionTotal} (f : x ⟶ y) :
    E.inflation (E.extensionProjectionSpan f).r := (E.extensionProjectionSpan f).wr

example {x y : E.ExtensionTotal} (f : x ⟶ y) :
    Q.of E.deflation E.inflation (E.extensionProjectionObject x) ⟶
      Q.of E.deflation E.inflation (E.extensionProjectionObject y) := E.extensionProjectionQMap f
