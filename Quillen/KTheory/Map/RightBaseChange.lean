/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
public import Quillen.KTheory.Map.NaturalIso

/-!
# Functor laws for original right-module change-of-rings K-maps

The actual change-of-rings exact functors satisfy identity and composition up
to their existing natural isomorphisms. Natural-isomorphism invariance of the
original strictly rebased `ExactFunctor.KMap` gives strict identity and
composition laws in every K-degree. All rings lie in the same universe; no
flatness or nontriviality assumption is used.
-/

@[expose] public section

noncomputable section

universe u

namespace Quillen.FiniteProjectiveModule

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- Identity change of rings induces the identity on the original right-module K-group. -/
@[simp]
theorem rightBaseChangeExact_KMap_id (R : Type u) [Ring R] (n : ℕ) :
    (rightBaseChangeExact (RingHom.id R)).KMap n =
      MonoidHom.id ((exactStructure Rᵐᵒᵖ).K n) :=
  (ExactFunctor.KMap_eq_of_natIso
    (F := rightBaseChangeExact (RingHom.id R))
    (G := ExactFunctor.id (exactStructure Rᵐᵒᵖ)) rightBaseChangeId n).trans
      (ExactFunctor.KMap_id (exactStructure Rᵐᵒᵖ) n)

/-- Composition of ring homomorphisms induces the composite of the original K-maps. -/
@[simp]
theorem rightBaseChangeExact_KMap_comp (f : R →+* S) (g : S →+* T) (n : ℕ) :
    (rightBaseChangeExact (g.comp f)).KMap n =
      ((rightBaseChangeExact g).KMap n).comp ((rightBaseChangeExact f).KMap n) :=
  (ExactFunctor.KMap_eq_of_natIso
    (F := rightBaseChangeExact (g.comp f))
    (G := (rightBaseChangeExact f).comp (rightBaseChangeExact g))
    (rightBaseChangeComp f g).symm n).trans
      (ExactFunctor.KMap_comp (rightBaseChangeExact f) (rightBaseChangeExact g) n)

end Quillen.FiniteProjectiveModule
