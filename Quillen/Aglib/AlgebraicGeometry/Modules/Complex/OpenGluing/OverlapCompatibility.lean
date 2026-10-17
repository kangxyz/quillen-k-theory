/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.BinaryDescent

/-! # The original overlap homotopy of the constructed local models -/
@[expose] public section

open Quillen.CochainComplex


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes

/-- Actual homotopies of adjoint maps restrict back to homotopies of the original local maps. -/
def extensionByZeroMapHomotopyReflect {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : CochainComplex U.Modules ℤ} {L : CochainComplex X.Modules ℤ} {f g : K ⟶ (restrict j).obj L}
    (H : Homotopy (extensionByZeroMap j f) (extensionByZeroMap j g)) : Homotopy f g :=
  (Homotopy.ofEq (extensionByZeroMap_restrict j f).symm).trans
    ((((Scheme.Modules.restrictFunctor j).mapHomotopy H).compLeft
      ((extensionByZeroAdjunction j).unit.app K)).trans
      (Homotopy.ofEq (extensionByZeroMap_restrict j g)))

namespace OpenHomotopyGluing
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)
  {K : CochainComplex W.Modules ℤ} {A : CochainComplex U.Modules ℤ} {B : CochainComplex V.Modules ℤ}
  (α : K ⟶ (restrict a).obj A) (β : K ⟶ (restrict b).obj B)

/-- The adjoint of the original first local comparison is precisely the original cone inclusion. -/
theorem first_adjoint : extensionByZeroMap j (first a b j k h α β) =
    homotopyPushoutInl (left a j α) (right a b j k h β) :=
  ((extensionByZeroAdjunction j).homEquiv _ _).symm_apply_apply _

/-- The adjoint of the original second local comparison is the other cone inclusion. -/
theorem second_adjoint : extensionByZeroMap k (second a b j k h α β) =
    homotopyPushoutInr (left a j α) (right a b j k h β) :=
  ((extensionByZeroAdjunction k).homEquiv _ _).symm_apply_apply _

/-- The constructed local models retain the actual original overlap by a specified chain homotopy.
-/
def overlapHomotopy :
    Homotopy (α ≫ (restrict a).map (first a b j k h α β))
      (β ≫ (restrict b).map (second a b j k h α β) ≫
        (openSquareRestrictIso b a k j h.symm).hom.app (glued a b j k h α β)) := by
  apply extensionByZeroMapHomotopyReflect a
  apply extensionByZeroMapHomotopyReflect j
  rw [← left_target_eq a j α (first a b j k h α β),
    ← right_target_eq a b j k h β (second a b j k h α β), first_adjoint, second_adjoint]
  exact homotopyPushoutInclusionHomotopy (left a j α) (right a b j k h β)

end OpenHomotopyGluing
end Quillen.PerfectComplexes
