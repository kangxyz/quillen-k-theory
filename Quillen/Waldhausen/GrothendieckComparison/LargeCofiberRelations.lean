/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.CofiberRelations
public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-!
# Original cofiber relations in independent category universes

The actual common-universe functor transports a displayed cofibration pushout to the existing
small-category cofiber relation. Its original object-class comparison then gives the relation
in the unchanged K-zero group of the original category. No representative or new K-map is chosen.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original cofiber relation with independent object and morphism universes. -/
theorem kZeroObjectClass_cofiber_of_large {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    W.kZeroObjectClass B = W.kZeroObjectClass A * W.kZeroObjectClass Q := by
  apply (W.smallModelKEquiv 0).injective
  simp only [map_mul, smallModelKEquiv_objectClass]
  have hQ' : IsPushout (AsSmall.up.map i)
      (W.smallModel.isZero.from_ (AsSmall.up.obj A)) (AsSmall.up.map q)
      (W.smallModel.isZero.to_ (AsSmall.up.obj Q)) := by
    convert W.smallModel_up_exact.pushout hi hQ using 1
    all_goals first
      | rfl
      | exact W.smallModel.isZero.eq_of_src _ _
      | exact W.smallModel.isZero.eq_of_tgt _ _
  exact W.smallModel.kZeroObjectClass_cofiber
    (W.smallModel_up_exact.cofibration i hi) hQ'

/-- The original signed pushout relation with independent category universes. -/
theorem kZeroObjectClass_pushout_of_large {A B D Q : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ Q} {j : D ⟶ Q} (hi : W.cof i) (hQ : IsPushout i f g j) :
    W.kZeroObjectClass Q =
      W.kZeroObjectClass B * W.kZeroObjectClass D * (W.kZeroObjectClass A)⁻¹ := by
  apply (W.smallModelKEquiv 0).injective
  simp only [map_mul, map_inv, smallModelKEquiv_objectClass]
  exact W.smallModel.kZeroObjectClass_pushout
    (W.smallModel_up_exact.cofibration i hi) (W.smallModel_up_exact.pushout hi hQ)

end Quillen.Waldhausen.Structure
