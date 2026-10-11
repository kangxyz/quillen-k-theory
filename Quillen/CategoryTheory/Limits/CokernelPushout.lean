/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # An original cokernel is a pushout along any displayed zero object -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {A B Q Z : C} {f : A ⟶ B} {q : B ⟶ Q} (hfq : f ≫ q = 0)
  (hc : IsColimit (CokernelCofork.ofπ q hfq)) (hZ : IsZero Z)

include hfq hc in
/-- The specified cokernel and zero maps form their actual universal cofiber square. -/
theorem isPushout_of_isColimitCokernelCofork :
    IsPushout f (hZ.from_ A) q (hZ.to_ Q) := by
  have w : f ≫ q = hZ.from_ A ≫ hZ.to_ Q := by
    rw [hfq, hZ.eq_zero_of_src (hZ.to_ Q), comp_zero]
  have hzero (s : PushoutCocone f (hZ.from_ A)) : f ≫ s.inl = 0 := by
    rw [s.condition, hZ.eq_zero_of_src s.inr, comp_zero]
  apply IsPushout.of_isColimit (c := PushoutCocone.mk q (hZ.to_ Q) w)
  refine PushoutCocone.IsColimit.mk w
    (fun s => (CokernelCofork.IsColimit.desc' hc s.inl (hzero s)).1) ?_ ?_ ?_
  · intro s
    exact (CokernelCofork.IsColimit.desc' hc s.inl (hzero s)).2
  · intro s
    exact hZ.eq_of_src _ _
  · intro s m hm _
    apply Cofork.IsColimit.hom_ext hc
    exact hm.trans (CokernelCofork.IsColimit.desc' hc s.inl (hzero s)).2.symm

end CategoryTheory.Limits
