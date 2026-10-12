/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Independent client of the original scalar-extension universal property

The unchanged matrix-image change-of-rings functor represents semilinear maps
into arbitrary ambient right modules. The ring and target-module universes are
independent. No literal balanced tensor-product carrier identification is asserted.
-/
public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
universe u v w
namespace Consumer.RingScalarExtension

/-- The unchanged actual functor has the Hom equivalence in independent universes. -/
def originalHomEquiv {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (P : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) :
    (((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N) ≃+ (P.obj →ₛₗ[f.op] N) :=
  rightBaseChangeHomEquiv f P N

/-- Its forward function is precomposition by the genuine original presentation unit. -/
theorem originalHomEquiv_unit {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (P : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N) :
    originalHomEquiv f P N h = h.comp (rightBaseChangeUnit f P) :=
  rightBaseChangeHomEquiv_apply f P N h

/-- Any semilinear map into an arbitrary target has exactly one target-linear extension. -/
theorem originalLiftUnique {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (P : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : P.obj →ₛₗ[f.op] N) :
    ∃! k : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N,
      k.comp (rightBaseChangeUnit f P) = h :=
  rightBaseChange_existsUnique f P N h

/-- The same property uses actual restriction of scalars in a common carrier universe. -/
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (P : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) (N : ModuleCat.{u} Sᵐᵒᵖ) :
    (((rightBaseChange f).obj P).obj ⟶ N) ≃+
      (P.obj ⟶ (ModuleCat.restrictScalars f.op).obj N) :=
  rightBaseChangeModuleHomEquiv f P N

/-- Source naturality retains the actual unchanged functor on arbitrary module morphisms. -/
example {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
    {P Q : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ} (g : P ⟶ Q) :
    ((rightBaseChange f).map g).hom.hom.comp (rightBaseChangeUnit f P) =
      (rightBaseChangeUnit f Q).comp g.hom.hom :=
  rightBaseChangeUnit_naturality f g

/-- Arbitrary target morphisms commute with the original Hom equivalence. -/
example {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
    (P : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    {N N' : ModuleCat.{w} Sᵐᵒᵖ} (g : N ⟶ N')
    (h : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N) :
    rightBaseChangeHomEquiv f P N' (g.hom.comp h) =
      g.hom.comp (rightBaseChangeHomEquiv f P N h) :=
  rightBaseChangeHomEquiv_naturality_target f P g h

/-- A concrete noncommutative matrix ring allows arbitrary independently-universed targets. -/
example (P : FiniteProjectiveModule.Category.{0, 0} (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ)
    (N : ModuleCat.{w} (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ)
    (h : P.obj →ₛₗ[(RingHom.id (Matrix (Fin 2) (Fin 2) ℤ)).op] N) :
    ∃! k : ((rightBaseChange (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))).obj P).obj
        →ₗ[(Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ] N,
      k.comp (rightBaseChangeUnit (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ)) P) = h :=
  originalLiftUnique _ P N h

/-- The actual homomorphism from the integers to the zero ring also satisfies the property. -/
example (P : FiniteProjectiveModule.Category.{0, 0} ℤᵐᵒᵖ)
    (N : ModuleCat.{w} (ZMod 1)ᵐᵒᵖ) (h : P.obj →ₛₗ[(Int.castRingHom (ZMod 1)).op] N) :
    ∃! k : ((rightBaseChange (Int.castRingHom (ZMod 1))).obj P).obj →ₗ[(ZMod 1)ᵐᵒᵖ] N,
      k.comp (rightBaseChangeUnit (Int.castRingHom (ZMod 1)) P) = h :=
  originalLiftUnique _ P N h

end Consumer.RingScalarExtension
