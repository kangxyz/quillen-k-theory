/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.WeakArrow.KEquivalence

/-! # Original weak-arrow objects, commuting squares and connective maps -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace Quillen.Tests.WeakArrowFactorization
open Waldhausen

/-- The weak counit preserves its original target component literally. -/
theorem stored_original_arrow {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (W : Structure D) (F : C ⥤ D)
    (X : WeakArrow.Obj W F) : ((WeakArrow.counit W F).app X).hom.right = X.obj.hom := rfl

/-- Its source component is the actual identity, not just a weak replacement. -/
theorem unchanged_source {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (W : Structure D) (F : C ⥤ D)
    (X : WeakArrow.Obj W F) : ((WeakArrow.counit W F).app X).hom.left = 𝟙 X.obj.left := rfl

/-- Every inherited original pushout is a genuine target pushout, with exact original maps. -/
theorem original_target_pushout {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (V : Structure C) (W : Structure D) (F : C ⥤ D)
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    {A B E Q : WeakArrow.Obj W F} {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ Q} {j : E ⟶ Q}
    (hi : (WeakArrow.waldhausenStructure V W F hF).cof i) (h : IsPushout i f g j) :
    IsPushout i.hom.right f.hom.right g.hom.right j.hom.right :=
  (WeakArrow.target_exact V W F hF).pushout hi h

/-- Weakness of the unchanged target map detects both original components. -/
theorem actual_weak_reflection {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (V : Structure C) (W : Structure D) (F : C ⥤ D)
    (hF : IsExact V.cof V.weq W.cof W.weq F) [W.weq.HasTwoOutOfThreeProperty]
    (hr : ∀ {A B : C} (f : A ⟶ B), W.weq (F.map f) → V.weq f)
    {X Y : WeakArrow.Obj W F} (f : X ⟶ Y) (hf : W.weq f.hom.right) :
    V.weq f.hom.left ∧ W.weq f.hom.right := WeakArrow.target_reflects V W F hF hr f hf

section K
variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (F : C ⥤ D)
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The first comparison has the actual original source-projection KMap as inverse. -/
theorem original_K_inverse (n : ℕ) (x : (WeakArrow.waldhausenStructure V W F hF).K n) :
    (WeakArrow.diagonalKEquiv V W F hF n).symm x = KMap (WeakArrow.source_exact V W F hF) n x := rfl

/-- Both original projections give the unchanged exact functor KMap, including degree zero. -/
theorem original_K_factor (n : ℕ) (x : V.K n) :
    KMap (WeakArrow.target_exact V W F hF) n (WeakArrow.diagonalKEquiv V W F hF n x) =
      KMap hF n x := DFunLike.congr_fun (WeakArrow.KMap_factor V W F hF n) x

/-- A proved actual second-leg comparison yields bijectivity of the original functor map. -/
theorem original_K_transfer (n : ℕ)
    (h : Function.Bijective (KMap (WeakArrow.target_exact V W F hF) n)) :
    Function.Bijective (KMap hF n) := (WeakArrow.KMap_bijective_iff_target V W F hF n).mpr h
end K
end Quillen.Tests.WeakArrowFactorization
