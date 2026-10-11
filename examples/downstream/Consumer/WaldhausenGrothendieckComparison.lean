/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.Functor

/-! An independent client detects injectivity of the original exact-functor
map on genuine Waldhausen K₀ from precisely its original classical map. -/
@[expose] public section

noncomputable section
open CategoryTheory Quillen.Waldhausen
universe u
namespace Consumer.WaldhausenGrothendieckComparison
open AlgebraicGrothendieck
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (W : Structure C) (V : Structure D)

/-- Injectivity on all actual fine K₀ classes is equivalent to injectivity of
the unchanged classical weak-equivalence/cofibration-pushout group map. -/
theorem exact_functor_injective_iff (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F) :
    Function.Injective (KMap hF 0) ↔
      Function.Injective (AlgebraicGrothendieck.map W F hF) := by
  constructor
  · intro h a b hab
    apply Multiplicative.ofAdd.injective
    apply grothendieckToKZero_injective W
    apply h
    have ha := DFunLike.congr_fun (grothendieckToKZero_natural W V F hF)
      (Multiplicative.ofAdd a)
    have hb := DFunLike.congr_fun (grothendieckToKZero_natural W V F hF)
      (Multiplicative.ofAdd b)
    change KMap hF 0 (grothendieckToKZero W (Multiplicative.ofAdd a)) =
      grothendieckToKZero V
        (Multiplicative.ofAdd (AlgebraicGrothendieck.map W F hF a)) at ha
    change KMap hF 0 (grothendieckToKZero W (Multiplicative.ofAdd b)) =
      grothendieckToKZero V
        (Multiplicative.ofAdd (AlgebraicGrothendieck.map W F hF b)) at hb
    rw [ha, hb, hab]
  · intro h x y hxy
    apply kZeroToGrothendieck_injective W
    apply Multiplicative.toAdd.injective
    apply h
    have he := congrArg (kZeroToGrothendieck V) hxy
    rw [← kZeroToGrothendieck_natural W V F hF x,
      ← kZeroToGrothendieck_natural W V F hF y] at he
    exact congrArg Multiplicative.toAdd he

end Consumer.WaldhausenGrothendieckComparison
