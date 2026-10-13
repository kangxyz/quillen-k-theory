/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Category.ModuleCat.MatrixImageFunctor
public import Mathlib.CategoryTheory.Whiskering

/-!
# Change of rings for actual finite projective right modules

Transporting entrywise matrix change of rings along the proved image equivalence
gives functors for arbitrary ring homomorphisms. The identity and composition
comparisons are natural isomorphisms, because choosing presentations is not
strictly functorial on the underlying modules.
-/
@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace Quillen.FiniteProjectiveModule

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- Change of rings on actual finite projective right modules via their proved matrix model. -/
def rightBaseChange (f : R →+* S) : Category.{u,u} Rᵐᵒᵖ ⥤ Category.{v,v} Sᵐᵒᵖ :=
  RightMatrix.imageEquivalence.inverse ⋙ RightMatrix.baseChange f ⋙
    RightMatrix.imageEquivalence.functor

/-- Changing rings along the identity recovers the original module naturally. -/
def rightBaseChangeId : rightBaseChange (RingHom.id R) ≅ 𝟭 (Category.{u,u} Rᵐᵒᵖ) :=
  RightMatrix.imageEquivalence.counitIso

/-- Consecutive changes of rings agree naturally with the composite ring homomorphism. -/
def rightBaseChangeComp (f : R →+* S) (g : S →+* T) :
    rightBaseChange f ⋙ rightBaseChange g ≅ rightBaseChange (g.comp f) :=
  Functor.isoWhiskerLeft RightMatrix.imageEquivalence.inverse
    (Functor.isoWhiskerLeft (RightMatrix.baseChange f)
      (Functor.isoWhiskerRight (RightMatrix.imageEquivalence (R := S)).unitIso.symm
        (RightMatrix.baseChange g ⋙ RightMatrix.imageEquivalence.functor)))

end Quillen.FiniteProjectiveModule
