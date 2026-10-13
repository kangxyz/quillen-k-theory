/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Devissage.Filtration

/-! # Exact functors carry actual finite filtrations to actual finite filtrations -/
@[expose] public section

noncomputable section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits

namespace Quillen.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D}

/-- Map every genuine short exact stage and its factor through an exact functor. -/
def mapFiltration (F : ExactFunctor E E') {P : ObjectProperty C} {Q : ObjectProperty D}
    (h : ∀ X, P X → Q (F.toFunctor.obj X)) {X : C} (G : E.Filtration P X) :
    E'.Filtration Q (F.toFunctor.obj X) := by
  induction G with
  | zero hX => exact .zero (F.toFunctor.map_isZero hX)
  | step S hS G hP ih => exact .step (S.map F.toFunctor) (F.map_conflation S hS) ih (h _ hP)

end Quillen.ExactFunctor
