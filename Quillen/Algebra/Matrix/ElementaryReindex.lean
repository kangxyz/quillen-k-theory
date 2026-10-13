/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Matrix.Elementary
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing elementary subgroups

A bijection of finite index sets induces an isomorphism of matrix unit groups
which carries each elementary generator to the generator with the reindexed
positions. It therefore carries the actual elementary subgroup onto the
elementary subgroup. All statements allow noncommutative coefficient rings.
-/
@[expose] public section

universe u v w

namespace Quillen.ElementaryMatrix

variable {R : Type u} [Ring R] {n : Type v} {m : Type w}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Relabel the rows and columns of a matrix unit by the same equivalence. -/
def reindex (e : n ≃ m) : (Matrix n n R)ˣ ≃* (Matrix m m R)ˣ :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

@[simp] lemma reindex_unit (e : n ≃ m) (i j : n) (hij : i ≠ j) (a : R) :
    reindex e (unit i j hij a) = unit (e i) (e j) (by simpa using hij) a := by
  apply Units.ext
  change Matrix.reindexRingEquiv R e (1 + Matrix.single i j a) =
    1 + Matrix.single (e i) (e j) a
  rw [map_add, map_one]
  congr 1
  exact Matrix.submatrix_single_equiv e.symm e.symm i j a

lemma reindex_subgroup_le (e : n ≃ m) :
    (subgroup n R).map (reindex e).toMonoidHom ≤ subgroup m R := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, j, hij, a, rfl⟩
  change reindex e (unit i j hij a) ∈ subgroup m R
  rw [reindex_unit]
  exact unit_mem_subgroup _ _ _ _

/-- Reindexing carries the elementary subgroup onto the elementary subgroup. -/
theorem reindex_subgroup (e : n ≃ m) :
    (subgroup n R).map (reindex e).toMonoidHom = subgroup m R := by
  apply le_antisymm (reindex_subgroup_le e)
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, j, hij, a, rfl⟩
  have h : e.symm i ≠ e.symm j := by simpa using hij
  refine ⟨unit (e.symm i) (e.symm j) h a, unit_mem_subgroup _ _ _ _, ?_⟩
  change reindex e (unit (e.symm i) (e.symm j) h a) = unit i j hij a
  simp

end Quillen.ElementaryMatrix
