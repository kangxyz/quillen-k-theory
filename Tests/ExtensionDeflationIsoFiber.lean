/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.ExactCategory.ExtensionDeflationEntry
/-! # Consumers of the actual fixed-deflation fiber equivalence -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Tests
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (X : C)
example : (E.extensionDeflationIsoFiber X).IsEquivalence := inferInstance
example : (E.extensionDeflationIsoFiberEquivalence X).functor =
    E.extensionDeflationIsoFiber X := rfl
example (p : E.ExtensionFiber X) :
    ((E.extensionDeflationIsoFiber X).obj p).obj.hom =
      (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)).inv := rfl
example {p q : E.ExtensionFiber X} (f : p ⟶ q) :
    ((E.extensionDeflationIsoFiber X).map f).hom.right.base.hom = f.iso.hom.hom.left := rfl
end Quillen.Tests
