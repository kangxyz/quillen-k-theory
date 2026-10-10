/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.ArrowCategory.Structure

/-! # Exact functors on the genuine arrow Waldhausen category -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
namespace ArrowCategory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}

theorem isZero_of_components (X : Arrow D) (hl : IsZero X.left) (hr : IsZero X.right) : IsZero X
    where
  unique_to Y := by
    refine ⟨{ default := Arrow.homMk (hl.to_ _) (hr.to_ _) (hl.eq_of_src _ _), uniq := ?_ }⟩
    intro f
    exact Arrow.hom_ext _ _ (hl.eq_of_src _ _) (hr.eq_of_src _ _)
  unique_from Y := by
    refine ⟨{ default := Arrow.homMk (hl.from_ _) (hr.from_ _) (hr.eq_of_tgt _ _), uniq := ?_ }⟩
    intro f
    exact Arrow.hom_ext _ _ (hl.eq_of_tgt _ _) (hr.eq_of_tgt _ _)

theorem mapArrow_exact (hF : IsExact V.cof V.weq W.cof W.weq F) :
    IsExact (waldhausenStructure V).cof (waldhausenStructure V).weq
      (waldhausenStructure W).cof (waldhausenStructure W).weq F.mapArrow where
  zero h := isZero_of_components _ (hF.zero ((source_exact V).zero h))
    (hF.zero ((target_exact V).zero h))
  cofibration _ hf := ⟨hF.cofibration _ hf.1, hF.cofibration _ hf.2⟩
  weak _ hf := ⟨hF.weak _ hf.1, hF.weak _ hf.2⟩
  pushout hf h := isPushout_of_pointwise _ _ _ _
    (hF.pushout hf.1 (pointwise_of_isPushout V hf h).1)
    (hF.pushout hf.2 (pointwise_of_isPushout V hf h).2)
end ArrowCategory
end Quillen.Waldhausen
