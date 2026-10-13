/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChange
import Mathlib.Algebra.Ring.PUnit

/-! Change of rings acts on actual right modules, with proved presentation independence. -/

noncomputable section

universe u v w

open CategoryTheory Quillen.RightMatrix Quillen.FiniteProjectiveModule

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

example (f : R →+* S) (P : ProjectiveMatrices R) :
    ((baseChange f).obj P).p = P.p.map f := baseChange_obj_matrix f P

example (f : R →+* S) (g : S →+* T) :
    baseChange (g.comp f) = baseChange f ⋙ baseChange g := baseChange_comp f g

example {P Q : ProjectiveMatrices R}
    (f : (linearMap P.p).range →ₗ[Rᵐᵒᵖ] (linearMap Q.p).range) :
    imageMap (liftImageMap f) = f := imageMap_liftImageMap f

example {P Q : ProjectiveMatrices R} (a : P ⟶ Q) :
    liftImageMap (imageMap a) = a := liftImageMap_imageMap a

example (M : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :
    (rightBaseChange (RingHom.id R)).obj M ≅ M := rightBaseChangeId.app M

example (f : R →+* S) (g : S →+* T)
    (M : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :
    (rightBaseChange g).obj ((rightBaseChange f).obj M) ≅
      (rightBaseChange (g.comp f)).obj M := (rightBaseChangeComp f g).app M

example : (imageFunctor (R := Matrix (Fin 2) (Fin 2) ℤ)).IsEquivalence := inferInstance

example : (imageFunctor (R := PUnit)).IsEquivalence := inferInstance
