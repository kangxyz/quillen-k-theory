/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Functor

/-! # Compatible dual Waldhausen structures

The compatibility is on literal weak maps and actual zero-corner kernel–cokernel
squares. No statement about S-constructions or K-theory is part of this input.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace Quillen.Waldhausen

/-- The exact structural compatibility required to reverse quotient grids. -/
structure IsCompatibleDual {C : Type u} [Category.{v} C]
    (W : Structure C) (Wd : Structure Cᵒᵖ) : Prop where
  weak {A B : C} (f : A ⟶ B) : W.weq f ↔ Wd.weq f.op
  cofiber {A B Z Q : C} (i : A ⟶ B) (z : A ⟶ Z) (q : B ⟶ Q) (s : Z ⟶ Q)
    (hZ : IsZero Z) :
    (W.cof i ∧ IsPushout i z q s) ↔ (Wd.cof q.op ∧ IsPullback i z q s)


/-- Maps out of any actual zero object are cofibrations. -/
theorem Structure.cof_of_isZero {C : Type u} [Category.{v} C]
    (W : Structure C) {Z X : C} (hZ : IsZero Z) (f : Z ⟶ X) : W.cof f := by
  let e := hZ.iso W.isZero
  have hf : f = e.hom ≫ W.isZero.to_ X := hZ.eq_of_src _ _
  rw [hf]
  exact W.cof.comp_mem _ _ (W.cof_iso _ inferInstance) (W.cof_zero _)

end Quillen.Waldhausen
