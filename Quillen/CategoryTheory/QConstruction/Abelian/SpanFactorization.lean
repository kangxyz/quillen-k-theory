/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.QConstruction.Abelian.CospanComposition

/-! # The epi-then-mono factorization of an actual abelian Q-span -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Q
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma span_factorization {X Y : C} (s : AbelianSpan X Y) :
    surjectionArrow s.l ≫ inflationArrow s.r = mkHom _ _ s := by
  let sq : IsPullback (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  symm
  apply mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst (𝟙 s.apex) (𝟙 s.apex) ≫ s.l = s.l
    simp
  · change sq.isoPullback.hom ≫ pullback.snd (𝟙 s.apex) (𝟙 s.apex) ≫ s.r = s.r
    simp

end Quillen.Q
