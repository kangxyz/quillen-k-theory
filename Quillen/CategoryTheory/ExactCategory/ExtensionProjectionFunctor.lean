/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.ExactCategory.ExtensionProjectionIdentity
public import Quillen.CategoryTheory.ExactCategory.ExtensionProjectionComposition

/-!
# The actual extension projection to the original Q construction

Both functor laws are proved for the original Q quotient and its genuine
pullback composition. Theorem B's comma-transition condition and the relation
between the strict fibers and extension groupoids remain further theorems.
-/
@[expose] public section
noncomputable section
universe v u
open CategoryTheory
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- Grayson's extension projection, with the original exact-category Q target. -/
def extensionProjection : E.ExtensionTotal ⥤ Quillen.Q E.deflation E.inflation where
  obj := E.extensionProjectionQObj
  map := E.extensionProjectionQMap
  map_id := E.extensionProjectionQMap_id
  map_comp := E.extensionProjectionQMap_comp

end Quillen.ExactStructure
