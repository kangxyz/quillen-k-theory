/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.Equivalence
public import Quillen.Waldhausen.KFunctor

/-! # The canonical natural isomorphism for general Waldhausen K₀

The original classical weak-arrow/cofibration-pushout presentation is naturally
isomorphic to the original fine homotopical K₀ functor on all small Waldhausen
categories and all exact functors. Both components are the original public maps.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace Quillen.Waldhausen.SmallWaldhausenCategory
open AlgebraicGrothendieck

/-- The original classical Grothendieck presentation on all small Waldhausen categories. -/
def grothendieckFunctor : SmallWaldhausenCategory.{u} ⥤ GrpCat.{u} where
  obj C := GrpCat.of (Multiplicative (AlgebraicGrothendieck.Group C.waldhausen))
  map F := GrpCat.ofHom (AlgebraicGrothendieck.map _ F.toFunctor F.isExact).toMultiplicative
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro a
    change (AlgebraicGrothendieck.map C.waldhausen (𝟭 C.Obj)
      (IsExact.id _ _)).toMultiplicative a = a
    rw [AlgebraicGrothendieck.map_id]
    rfl
  map_comp F G := by
    apply ConcreteCategory.hom_ext
    intro a
    change (AlgebraicGrothendieck.map _ (F.toFunctor ⋙ G.toFunctor)
      (F.isExact.comp G.isExact)).toMultiplicative a =
        (AlgebraicGrothendieck.map _ G.toFunctor G.isExact).toMultiplicative
          ((AlgebraicGrothendieck.map _ F.toFunctor F.isExact).toMultiplicative a)
    rw [AlgebraicGrothendieck.map_comp]
    rfl

/-- The original object-class comparison is a genuine natural isomorphism to
the existing actual fine Waldhausen K₀ and its original exact-functor maps. -/
def grothendieckKZeroIso : grothendieckFunctor.{u} ≅ KFunctor 0 :=
  NatIso.ofComponents (fun C ↦ (grothendieckKZeroEquiv C.waldhausen).toGrpIso) (by
    intro C D F
    apply ConcreteCategory.hom_ext
    intro a
    exact (DFunLike.congr_fun
      (grothendieckToKZero_natural C.waldhausen D.waldhausen F.toFunctor F.isExact) a).symm)

/-- The forward component is exactly the original object-loop homomorphism. -/
@[simp] theorem grothendieckKZeroIso_hom_app (C : SmallWaldhausenCategory.{u}) :
    grothendieckKZeroIso.hom.app C = GrpCat.ofHom (grothendieckToKZero C.waldhausen) := rfl

/-- The inverse component is exactly the original realized grading map. -/
@[simp] theorem grothendieckKZeroIso_inv_app (C : SmallWaldhausenCategory.{u}) :
    grothendieckKZeroIso.inv.app C = GrpCat.ofHom (kZeroToGrothendieck C.waldhausen) := rfl

end Quillen.Waldhausen.SmallWaldhausenCategory
