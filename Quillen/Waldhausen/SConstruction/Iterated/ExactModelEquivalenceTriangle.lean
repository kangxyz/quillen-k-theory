/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence

/-! # The actual normalized inverse retains the original categorical triangle

Both comparisons use the same chosen-zero normalization isomorphism. Its two
opposite factors cancel before the original equivalence triangle is applied.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
namespace Quillen.Waldhausen.IteratedS.ExactModelEquivalence
variable {V W : Model.{u}} (e : V ≌ W)
  (hF : IsExact V.waldhausen.cof V.waldhausen.weq
    W.waldhausen.cof W.waldhausen.weq e.functor)
  (hG : IsExact W.waldhausen.cof W.waldhausen.weq
    V.waldhausen.cof V.waldhausen.weq e.inverse)
  (h0 : e.functor.obj V.waldhausen.zero = W.waldhausen.zero)

/-- Forward evaluation of the actual normalized unit cancels its actual counit. -/
theorem forward_unit_counit (X : V) :
    (forward e hF h0).functor.map ((unitIso e hF hG h0).inv.app X) ≫
      (counitIso e hF hG h0).hom.app ((forward e hF h0).functor.obj X) =
        𝟙 ((forward e hF h0).functor.obj X) :=
  (e.changeInverse
    (Quillen.rebaseFunctorIso e.inverse W.waldhausen.zero V.waldhausen.zero
      ((hG.zero W.waldhausen.isZero).iso V.waldhausen.isZero))).functor_unitIso_comp X

/-- The other actual triangle retains the same normalized inverse on its original objects. -/
theorem backward_unit_counit (Y : W) :
    (unitIso e hF hG h0).inv.app ((backward e hG).functor.obj Y) ≫
      (backward e hG).functor.map ((counitIso e hF hG h0).hom.app Y) =
        𝟙 ((backward e hG).functor.obj Y) :=
  (e.changeInverse
    (Quillen.rebaseFunctorIso e.inverse W.waldhausen.zero V.waldhausen.zero
      ((hG.zero W.waldhausen.isZero).iso V.waldhausen.isZero))).unit_inverse_comp Y

end Quillen.Waldhausen.IteratedS.ExactModelEquivalence
