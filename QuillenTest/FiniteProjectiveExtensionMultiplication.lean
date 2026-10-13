/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveExtensionMultiplication

/-! # Actual fixed-quotient action multiplication regression tests -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction
variable (R : Type u) [Ring R] (C : Category.{u, u} R)

example : ExtensionActionCategory R C × ExtensionActionCategory R C ⥤
    ExtensionActionCategory R C := extensionActionMultiplication R C

example (p q : ExtensionActionCategory R C) :
    ((extensionActionMultiplication R C).obj (p, q)).obj.of.obj.left =
      pullback p.obj.of.obj.hom q.obj.of.obj.hom := rfl

example (S T : IsoCategory R) (p q : (exactStructure R).ExtensionFiber C) :
    (S ⊗ T) ⊙ₗ extensionProductFiber R p q ≅
      extensionProductFiber R (S ⊙ₗ p) (T ⊙ₗ q) := extensionAddProductIso R S T p q

example (p q : (exactStructure R).ExtensionOver C)
    (k : (exactStructure R).ExtensionKernelData p) (l : (exactStructure R).ExtensionKernelData q) :
    (exactStructure R).ExtensionKernelData ((exactStructure R).extensionProductObj p q) :=
  (exactStructure R).extensionProductKernelData p q k l

example {p p' p'' q q' q'' : ExtensionActionCategory R C}
    (f : p ⟶ p') (g : p' ⟶ p'') (f' : q ⟶ q') (g' : q' ⟶ q'') :
    extensionProductHom R (f ≫ g) (f' ≫ g') =
      extensionProductHom R f f' ≫ extensionProductHom R g g' :=
  extensionProductHom_comp R f g f' g'

end Quillen.FiniteProjectiveModule
