/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveExtensionConnected

/-! # Genuine fixed-quotient product and connectedness regression tests -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction
variable (R : Type u) [Ring R] (C : Category.{u, u} R)

example : IsConnected (ExtensionActionCategory R C) := extensionActionCategory_isConnected R C

example (p : (exactStructure R).ExtensionFiber C) :
    (⟨(exactStructure R).extensionUnit C⟩ : ExtensionActionCategory R C) ⟶ ⟨p⟩ :=
  extensionUnitTo R p

example (p : (exactStructure R).ExtensionFiber C) :
    extensionKernelIsoObject R p ⊙ₗ (exactStructure R).extensionUnit C ≅ p :=
  extensionSplitIso R p

example (p q : (exactStructure R).ExtensionOver C) :
    ((exactStructure R).extensionProductObj p q).obj.left =
      pullback p.obj.hom q.obj.hom := rfl

example (p q : (exactStructure R).ExtensionOver C) :
    (exactStructure R).deflation ((exactStructure R).extensionProductObj p q).obj.hom :=
  ((exactStructure R).extensionProductObj p q).property

example (p : (exactStructure R).ExtensionOver C) :
    p ⟶ (exactStructure R).extensionProductObj p p :=
  (exactStructure R).extensionDiagonal p

end Quillen.FiniteProjectiveModule
