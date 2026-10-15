/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.CategoryTheory.ExactCategory.Basic
import Quillen.CategoryTheory.ExactCategory.ExtensionBaseChange

open CategoryTheory.ExactCategory


/-! # Original Q-span transport on the actual extension fibers -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

example {X Y : C} (f : X ⟶ Y) : E.ExtensionFiber Y ⥤ E.ExtensionFiber X :=
  E.extensionFiberPullback f

example {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.ExtensionFiber Y ⥤ E.ExtensionFiber X := E.extensionSpanTransport s
