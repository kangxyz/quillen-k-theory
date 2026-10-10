/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Duality.SConstruction
import Quillen.Waldhausen.Approximation.GeneralKEquivalence

/-! # Dual approximation for the original S-construction map

Actual right-to-left factorization supplies App2 in the opposite category.
The original S-map is recovered by the proved natural coordinate reversal,
and its original canonical K-map is bijective. All cylinder and dual exactness
inputs remain structural and explicit; no K-equivalence is a hypothesis.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen

/-- Dual App1/App2, with the actual incoming arrow and strict original equation. -/
structure HasDualApproximationProperty {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (W : Structure C) (V : Structure D)
    (fib : MorphismProperty C) (F : C ⥤ D) : Prop where
  reflects {A B : C} (f : A ⟶ B) : V.weq (F.map f) → W.weq f
  lift {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      fib i ∧ V.weq p ∧ p ≫ F.map i = f

section General
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd) {F : C ⥤ D}

namespace IsCompatibleDual
include hW

/-- The opposite weak class is exactly reversal of the original weak class. -/
theorem weq_eq_op : Wd.weq = W.weq.op := by
  funext A B f
  exact propext (hW.weak f.unop).symm

/-- Original saturation also holds in the literal dual weak class. -/
theorem dual_saturated [W.weq.HasTwoOutOfThreeProperty] :
    Wd.weq.HasTwoOutOfThreeProperty := by
  rw [weq_eq_op hW]
  infer_instance

end IsCompatibleDual

namespace HasDualApproximationProperty
variable (h : HasDualApproximationProperty W V Wd.cof.unop F)
include h hW hV

/-- Strict incoming factorization is actual App2 for the opposite functor. -/
theorem op : HasApproximationProperty Wd Vd F.op where
  reflects f hf := (hW.weak f.unop).mp (h.reflects f.unop ((hV.weak _).mpr hf))
  lift {X Y} f := by
    obtain ⟨X', i, p, hi, hp, eq⟩ := h.lift f.unop
    exact ⟨Opposite.op X', i.op, p.op, hi, (hV.weak _).mp hp,
      congrArg Quiver.Hom.op eq⟩

end HasDualApproximationProperty

end General

section SameUniverses
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hW : IsCompatibleDual W Wd)
  (hV : IsCompatibleDual V Vd) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (h : HasDualApproximationProperty W V Wd.cof.unop F)
  [V.weq.HasTwoOutOfThreeProperty]
  (Jd : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
include hW hV hFd h Jd

/-- Dual approximation proves complete weakness of the unchanged original realization map. -/
theorem deloopingMap_isWeakHomotopyEquivalence_of_dualApproximation :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom := by
  let := hV.dual_saturated
  exact DualSConstruction.sSetMap_weak_of_dual hW hV hF hFd
    ((h.op hW hV).deloopingMap_isWeakHomotopyEquivalence_general hFd Jd)

/-- The actual original K-homomorphism is bijective in every connective degree. -/
theorem KMap_bijective_of_dualApproximation (n : ℕ) :
    Function.Bijective (KMap hF n) :=
  KMap_bijective_of_isWeakHomotopyEquivalence hF
    (deloopingMap_isWeakHomotopyEquivalence_of_dualApproximation hW hV hF hFd h Jd) n

/-- The dual approximation equivalence has exactly the original K-map as forward map. -/
def KEquivOfDualApproximation (n : ℕ) : W.K n ≃* V.K n :=
  MulEquiv.ofBijective (KMap hF n)
    (KMap_bijective_of_dualApproximation hW hV hF hFd h Jd n)

@[simp] theorem KEquivOfDualApproximation_toMonoidHom (n : ℕ) :
    (KEquivOfDualApproximation hW hV hF hFd h Jd n).toMonoidHom = KMap hF n := rfl

end SameUniverses
end Quillen.Waldhausen
