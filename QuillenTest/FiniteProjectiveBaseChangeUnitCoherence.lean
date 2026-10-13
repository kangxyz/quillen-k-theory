/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUnitCoherence
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Original scalar-extension unit regression tests

These tests use the original identity and composition comparisons, including
an explicit noncommutative matrix ring and extension into the zero ring.
-/

@[expose] public section

noncomputable section

universe u v w

open MulOpposite Quillen.FiniteProjectiveModule

namespace FiniteProjectiveBaseChangeUnitCoherenceTest

example {R : Type u} [Ring R] (P : Category.{u, u} Rᵐᵒᵖ) (x : P.obj) :
    (rightBaseChangeId.hom.app P).hom.hom (rightBaseChangeUnit (RingHom.id R) P x) = x :=
  rightBaseChangeId_hom_unit P x

example {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (P : Category.{u, u} Rᵐᵒᵖ) (x : P.obj) :
    ((rightBaseChangeComp f g).hom.app P).hom.hom
        (rightBaseChangeUnit g ((rightBaseChange f).obj P) (rightBaseChangeUnit f P x)) =
      rightBaseChangeUnit (g.comp f) P x :=
  rightBaseChangeComp_hom_unit f g P x

/-- Noncommutative coefficients make the order of consecutive right actions explicit. -/
abbrev Coefficients := Matrix (Fin 2) (Fin 2) ℤ

example (P : Category Coefficientsᵐᵒᵖ) (x : P.obj) (s t : Coefficients) :
    ((rightBaseChangeComp (RingHom.id Coefficients) (RingHom.id Coefficients)).hom.app P).hom.hom
        (rightBaseChangeUnit (RingHom.id Coefficients)
          ((rightBaseChange (RingHom.id Coefficients)).obj P)
          (rightBaseChangeUnit (RingHom.id Coefficients) P (op t • (op s • x)))) =
      op (s * t) • rightBaseChangeUnit (RingHom.id Coefficients) P x := by
  rw [rightBaseChangeComp_hom_unit]
  change rightBaseChangeUnit (RingHom.id Coefficients) P (op t • (op s • x)) = _
  rw [smul_smul]
  exact (rightBaseChangeUnit (RingHom.id Coefficients) P).map_smulₛₗ (op (s * t)) x

example {R : Type u} [Ring R] (f : R →+* ZMod 1)
    (P : Category.{u, u} Rᵐᵒᵖ) (x : P.obj) :
    ((rightBaseChangeComp f (RingHom.id (ZMod 1))).hom.app P).hom.hom
        (rightBaseChangeUnit (RingHom.id (ZMod 1)) ((rightBaseChange f).obj P)
          (rightBaseChangeUnit f P x)) = 0 := by
  rw [rightBaseChangeComp_hom_unit]
  let := Module.subsingleton (ZMod 1)ᵐᵒᵖ
    ((rightBaseChange ((RingHom.id (ZMod 1)).comp f)).obj P).obj
  exact Subsingleton.elim _ _

end FiniteProjectiveBaseChangeUnitCoherenceTest
