/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.ExactCategory.ExtensionProjection
public import Quillen.CategoryTheory.ExactCategory.ExtensionQuotientSpanCharacterization

/-! # Identity law for the actual extension quotient assignment -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- Identity extensions induce the identity in the original Q quotient. -/
@[simp] theorem extensionProjectionQMap_id (x : E.ExtensionTotal) :
    E.extensionProjectionQMap (𝟙 x) = 𝟙 (E.extensionProjectionQObj x) := by
  change Quillen.Q.mkHom E.deflation E.inflation (E.extensionProjectionSpan (𝟙 x)) =
    Quillen.Q.mkHom E.deflation E.inflation (Span.id (E.extensionProjectionObject x))
  unfold extensionProjectionSpan
  apply QuotientSpan.mkHom_eq_of_cokernel
    (p := (E.extensionQuotientData x).π)
    (zp := by simpa [Quillen.Subdivision.domainMap] using (E.extensionQuotientData x).zero)
  · exact CokernelCofork.isColimitOfIsColimitOfIff'
      ((E.extensionQuotientData x).isColimit E) _ (by
        intro W a
        simp [Quillen.Subdivision.domainMap])
  · simp
  · simp

end CategoryTheory.ExactCategory.ExactStructure
