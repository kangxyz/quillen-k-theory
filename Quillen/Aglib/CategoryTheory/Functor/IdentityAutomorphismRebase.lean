/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.Rebase
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismSquare
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-!
# Identity automorphisms under actual functor rebasing

The original object replacement and conjugated functor preserve the same supplied identity
automorphisms. All category, object and isomorphism data and the preservation hypothesis
are unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u₁ v₁
open CategoryTheory
open Quillen.FunctorIdentityAutomorphism
namespace Quillen.PerfectComplexes
theorem rebase_preserves {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    (F : C ⥤ D) (x : C) (y : D) (e : F.obj x ≅ y)
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves F α β) :
    Preserves (Quillen.rebaseFunctor F x y e) α β :=
  map_hom_eq_of_iso (Quillen.rebaseFunctor F x y e) F
    (Quillen.rebaseFunctorIso F x y e).symm α β h


end Quillen.PerfectComplexes
end
end
