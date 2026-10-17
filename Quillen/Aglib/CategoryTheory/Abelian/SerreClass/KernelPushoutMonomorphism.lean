/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.Abelian.SerreClass.KernelPushoutComparison
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact

/-!
# Monicity of the actual kernel-pushout extension map

A prescribed monomorphism from the old kernel induces the original monomorphic
map of extension middle objects, with its literal pushout formula.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

instance kernelPushoutOverHom_mono {N : C} (X : Over N) {U : C}
    (i : (overKernel N).obj X ⟶ U) [Mono i] : Mono (kernelPushoutOverHom X i).left :=
  inferInstanceAs (Mono (pushout.inl (overKernelι X) i))

end Quillen.SerreLocalization
