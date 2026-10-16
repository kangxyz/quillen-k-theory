/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Quillen.Aglib.LinearAlgebra.Matrix.ElementaryReindex
public import Quillen.Aglib.LinearAlgebra.Matrix.BlockWhitehead

/-! # Elementary matrices under finite stabilization

The original finite-rank transition is the relabelled block sum with
an identity, and elementary generators retain their original coordinates.
-/
@[expose] public section

universe u
namespace Quillen.StableGeneralLinear
variable (R : Type u) [Ring R]

/-- Stabilization preserves the original positions of an elementary matrix. -/
lemma step_unit (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R) :
    step R n (ElementaryMatrix.unit i j hij a) =
      ElementaryMatrix.unit i.castSucc j.castSucc (by simpa using hij) a := by
  change ElementaryMatrix.reindex finSumFinEquiv
    (ElementaryMatrix.blockSum (ElementaryMatrix.unit i j hij a)
      (1 : (Matrix (Fin 1) (Fin 1) R)ˣ)) = _
  rw [ElementaryMatrix.blockSum_unit_one, ElementaryMatrix.reindex_unit]
  rfl

/-- The concrete transition is the relabelled block sum with an identity. -/
lemma transition_eq_reindex_blockSum (n m : ℕ) (g : GL R n) :
    transition R n (n + m) (Nat.le_add_right n m) g =
      ElementaryMatrix.reindex finSumFinEquiv
        (ElementaryMatrix.blockSum g (1 : GL R m)) := by
  apply Units.ext
  exact transition_val_fromBlocks R n m g

end Quillen.StableGeneralLinear
