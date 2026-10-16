/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.LinearAlgebra.Matrix.RightScalarExtension
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of finite free right scalar extension

These consumers check the actual unit and uniqueness, target naturality, and
rectangular-matrix compatibility with independent ambient module universes.
Explicit noncommutative matrix rings, scalar extension to the zero ring, and
rank zero require no additional assumptions.
-/

@[expose] public section

noncomputable section

universe u v w a b

open Quillen.RightMatrix MulOpposite

namespace RightScalarExtensionTest

section ArbitraryRings

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable {N : Type w} [AddCommGroup N] [Module Sᵐᵒᵖ N]
variable {n : Type a} {m : Type b} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

example (f : R →+* S) (h : (n → R) →ₛₗ[f.op] N) :
    ∃! g : (n → S) →ₗ[Sᵐᵒᵖ] N, g.comp (coordinateBaseChange f) = h := by
  refine ⟨extendSemilinear f h, extendSemilinear_comp_coordinateBaseChange f h, ?_⟩
  intro g hg
  exact extendSemilinear_unique f h g hg

example (f : R →+* S) (h : (n → R) →ₛₗ[f.op] N) (y : n → S) :
    (freeScalarExtensionEquiv f).symm h y = ∑ i, op (y i) • h (Pi.single i 1) := rfl

example (f : R →+* S) (A : Matrix m n R) (h : (m → R) →ₛₗ[f.op] N) :
    extendSemilinear f (h.comp (linearMap A)) =
      (extendSemilinear f h).comp (linearMap (A.map f)) :=
  extendSemilinear_precomp_matrix f A h

example {N' : Type*} [AddCommGroup N'] [Module Sᵐᵒᵖ N'] (f : R →+* S)
    (h : (n → R) →ₛₗ[f.op] N) (g : N →ₗ[Sᵐᵒᵖ] N') :
    extendSemilinear f (g.comp h) = g.comp (extendSemilinear f h) :=
  extendSemilinear_postcomp f h g

end ArbitraryRings

section NoncommutativeRing

/-- A concrete noncommutative coefficient ring. -/
abbrev NoncommutativeRing := Matrix (Fin 2) (Fin 2) ℤ

example (A : Matrix (Fin 3) (Fin 2) NoncommutativeRing)
    (x : Fin 2 → NoncommutativeRing) :
    coordinateBaseChange (RingHom.id NoncommutativeRing) (linearMap A x) =
      linearMap (A.map (RingHom.id NoncommutativeRing))
        (coordinateBaseChange (RingHom.id NoncommutativeRing) x) :=
  coordinateBaseChange_linearMap _ A x

example (h : (Fin 3 → ℤ) →ₛₗ[(Int.castRingHom NoncommutativeRing).op]
    NoncommutativeRing) :
    (extendSemilinear (Int.castRingHom NoncommutativeRing) h).comp
        (coordinateBaseChange (Int.castRingHom NoncommutativeRing)) = h :=
  extendSemilinear_comp_coordinateBaseChange _ h

end NoncommutativeRing

section ZeroRing

example (h : (Fin 2 → ℤ) →ₛₗ[(Int.castRingHom (ZMod 1)).op] ZMod 1) :
    (freeScalarExtensionEquiv (Int.castRingHom (ZMod 1)))
        ((freeScalarExtensionEquiv (Int.castRingHom (ZMod 1))).symm h) = h :=
  (freeScalarExtensionEquiv (Int.castRingHom (ZMod 1))).apply_symm_apply h

example {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
    {N : Type w} [AddCommGroup N] [Module Sᵐᵒᵖ N]
    (h : (Fin 0 → R) →ₛₗ[f.op] N) (y : Fin 0 → S) :
    extendSemilinear f h y = 0 := by simp

end ZeroRing

end RightScalarExtensionTest
