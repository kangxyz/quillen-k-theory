/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-! # Original K-zero homomorphisms in independent universes

The existing actual small-model K-equivalence transports the object-generator
extensionality theorem back to the original category. Both the original object
classes and the specified up/down functors are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v w
namespace Quillen.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Original object loops determine K-zero homomorphisms without equating category universes. -/
theorem kZero_hom_ext_ofSmallModel {H : Type w} [_root_.Group H] (f g : W.K 0 →* H)
    (h : ∀ A, f (W.kZeroObjectClass A) = g (W.kZeroObjectClass A)) : f = g := by
  let e := W.smallModelKEquiv 0
  have hc : f.comp e.symm.toMonoidHom = g.comp e.symm.toMonoidHom := by
    apply kZero_hom_ext W.smallModel
    intro A
    have he : e.symm (W.smallModel.kZeroObjectClass A) =
        W.kZeroObjectClass (AsSmall.down.obj A) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, Structure.smallModelKEquiv_objectClass]
      rfl
    change f (e.symm (W.smallModel.kZeroObjectClass A)) =
      g (e.symm (W.smallModel.kZeroObjectClass A))
    rw [he]
    exact h (AsSmall.down.obj A)
  apply MonoidHom.ext
  intro a
  have ha := DFunLike.congr_fun hc (e a)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using ha

end Quillen.Waldhausen.AlgebraicGrothendieck
