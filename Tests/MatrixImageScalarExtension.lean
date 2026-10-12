/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Algebra.Category.ModuleCat.MatrixImageScalarExtension
public import Mathlib.Data.ZMod.Basic

/-! # Actual arbitrary-target scalar-extension consumers for matrix images -/
noncomputable section
open CategoryTheory Quillen.RightMatrix
universe u v w

example {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (P : ProjectiveMatrices R)
    (N : Type w) [AddCommGroup N] [Module Sᵐᵒᵖ N] :
    ((linearMap (P.p.map f)).range →ₗ[Sᵐᵒᵖ] N) ≃+
      ((linearMap P.p).range →ₛₗ[f.op] N) :=
  imageExtensionHomEquiv f P N

example {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) {P Q : ProjectiveMatrices R} (a : P ⟶ Q) :
    (imageMap ((baseChange f).map a)).comp (imageUnit f P) =
      (imageUnit f Q).comp (imageMap a) :=
  imageUnit_naturality_comp f a

example (P : ProjectiveMatrices (Matrix (Fin 2) (Fin 2) ℤ)) :
    ((linearMap (P.p.map (RingHom.id _))).range →ₗ[(Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ]
      Matrix (Fin 2) (Fin 2) ℤ) ≃+
    ((linearMap P.p).range →ₛₗ[(RingHom.id (Matrix (Fin 2) (Fin 2) ℤ)).op]
      Matrix (Fin 2) (Fin 2) ℤ) :=
  imageExtensionHomEquiv (RingHom.id _) P _

example (P : ProjectiveMatrices ℤ) :
    ((linearMap (P.p.map (Int.castRingHom (ZMod 1)))).range →ₗ[(ZMod 1)ᵐᵒᵖ] ZMod 1) ≃+
      ((linearMap P.p).range →ₛₗ[(Int.castRingHom (ZMod 1)).op] ZMod 1) :=
  imageExtensionHomEquiv (Int.castRingHom (ZMod 1)) P _
