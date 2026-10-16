/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.IdentitySequence

/-! Actual identity-sequence pushout inverse and literal chosen-zero component. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen Quillen.Waldhausen.Additivity
universe u v u' v'
namespace QuillenTest.IdentitySequence
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (F : C ⥤ D)

/-- The original target inclusion is the exact inverse of the relative comparison. -/
theorem original_target_inverse {X Y : C} (f : X ⟶ Y) :
    targetι W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) (Arrow.mk f) ≫
        (identityPushoutComparisonIso W F f).hom = 𝟙 (F.obj Y) := by
  rw [identityPushoutComparisonIso_hom]
  exact targetι_comparison W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) (Arrow.mk f)

/-- The quotient component is exactly the existing map to the specified target zero. -/
theorem original_zero_component (X : C) :
    (Functor.whiskerLeft F (QuotientRows.oneIdToZero W)).app X =
      W.isZero.from_ (F.obj X) := rfl

/-- The whole original zero-corner square is supplied for every actual exact functor. -/
theorem original_zero_pushout (hF : IsExact V.cof V.weq W.cof W.weq F) (X : C) :
    IsPushout (𝟙 (F.obj X)) (W.isZero.from_ (F.obj X))
      (W.isZero.from_ (F.obj X)) (W.isZero.to_ W.zero) :=
  (identityCofibrationSequence W F V hF).cofiber X

end QuillenTest.IdentitySequence
