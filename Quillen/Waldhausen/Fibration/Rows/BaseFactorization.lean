/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Fibration.Rows.ReflexiveFactorization

/-! # Genuine base factorization from the original fine joint cylinder

The actual endpoint coproduct and original joint cofibration provide the
first factor; the original fine weak projection supplies the second factor.
No additional chosen factorization is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Fibration.RowFactorization.JointData
variable {C : Type u} [Category.{v} C] {W : Structure C}
  (D : JointData (NestedWeakEquivalences.refl W))

/-- The original fine joint cylinder supplies a genuine factorization of every original arrow. -/
def sourceFactorization : FunctorialFactorization W where
  middle := D.joint ⋙ ExtensionCategory.middle W
  inclusion := D.inl ≫ Functor.whiskerLeft D.joint (ExtensionCategory.inclusion W)
  projection := D.projection
  factorization f := by
    change (D.inl.app f ≫ (D.joint.obj f).obj.hom) ≫ D.projection.app f = f.hom
    simpa only [Category.assoc] using D.factorization f
  cofibration f := W.cof.comp_mem _ _
    (W.cof_pushout (W.cof_zero f.right)
      (IsPushout.of_is_coproduct (D.coproduct f) W.isZero.isInitial).flip)
    (D.joint.obj f).property
  weak := D.weak

/-- Factorization retains the actual original projection rather than a newly chosen weak map. -/
@[simp] theorem sourceFactorization_projection (f : Arrow C) :
    (D.sourceFactorization).projection.app f = D.projection.app f := rfl
end Quillen.Waldhausen.Fibration.RowFactorization.JointData
