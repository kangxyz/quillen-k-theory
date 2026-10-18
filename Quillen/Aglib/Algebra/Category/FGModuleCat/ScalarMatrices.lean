/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix automorphisms of the actual finite-module category

Intended upstream owner: `Aglib.Algebra.Category.FGModuleCat.ScalarMatrices`.
Linear automorphisms of finite modules over any ring give their actual
finite-module automorphisms. Over a commutative ring, finite general linear
matrices act by ordinary multiplication on column vectors. The definitions
retain the expressions migrated from R5's `FGModuleCat/ScalarMatrices` source.
The current consumer is `Quillen.KTheory.Field.MatrixTransport`, which compares
the original stable right-module action with this standard finite-module action.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory

namespace FGModuleCat

/-- A linear automorphism gives the original finite-module isomorphism on the same carrier. -/
def linearAutToAut (R : Type u) [Ring R] (V : Type v) [AddCommGroup V]
    [Module R V] [Module.Finite R V] : (V ≃ₗ[R] V) →* Aut (FGModuleCat.of R V) where
  toFun e := e.toFGModuleCatIso
  map_one' := by apply Iso.ext; rfl
  map_mul' e f := by apply Iso.ext; rfl

/-- A finite invertible matrix acts on the original standard finite module. -/
def matrixToAut (R : Type u) [CommRing R] (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) R →* Aut (FGModuleCat.of R (Fin n → R)) :=
  (linearAutToAut R (Fin n → R)).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)).toMonoidHom.comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom)

/-- The action retains literal matrix multiplication on column vectors. -/
theorem matrixToAut_apply (R : Type u) [CommRing R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) (x : Fin n → R) :
    (matrixToAut R n g).hom x = g.val.mulVec x := Matrix.GeneralLinearGroup.toLin_apply g x

end FGModuleCat
