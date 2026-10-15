/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.CategoryTheory.ExactCategory.ExtensionDeflationSpan

/-! # Original contravariant Q-span and structured-comma consumers -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) {X Y : C} (s : Span E.deflation E.inflation X Y)

example : E.extensionSpanTransport s ⋙ E.extensionDeflationIsoFiber X ⋙
    IsoFiber.toStructured E.extensionProjection (Q.of E.deflation E.inflation X) ⟶
    E.extensionDeflationIsoFiber Y ⋙
      IsoFiber.toStructured E.extensionProjection (Q.of E.deflation E.inflation Y) ⋙
      StructuredArrow.map (T := E.extensionProjection) (Q.mkHom E.deflation E.inflation s) :=
  E.extensionDeflationSpanComma s

example (p : E.ExtensionFiber Y) :
    ((E.extensionDeflationSpanComma s).app p).right = E.extensionDeflationSpanHom s p := rfl

example (p : E.ExtensionFiber Y) :
    (E.qIsoOfIso (E.extensionOfDeflationQuotientIso
      ((E.extensionSpanTransport s).obj p).of)).inv ≫
        E.extensionProjectionQMap (E.extensionDeflationSpanHom s p) =
      Q.mkHom E.deflation E.inflation s ≫
        (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)).inv :=
  E.extensionDeflationSpanHom_over s p
