/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.CategoryTheory.ExactCategory.ExtensionProjectionIdentity

/-! # The original Q-arrow assignment preserves identities -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

example (x : E.ExtensionTotal) :
    E.extensionProjectionQMap (𝟙 x) = 𝟙 (E.extensionProjectionQObj x) := by simp
