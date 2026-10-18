/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.FiniteRootLifting
public import Mathlib.Tactic.NormNum
public import Quillen.Aglib.LinearAlgebra.Matrix.Elementary

/-!
# FiniteRootLifting

Canonical provider for the accepted interfaces described in the sections below.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## LiteralGL5Consumer -/

section

/-!
# Literal rational matrix consumer of the conditional finite-root reduction

The target group is the actual finite general linear group of dimension five.
The sections and product-one diagonal lifts are explicitly constructed. These
checks consume the generic reduction, rather than assuming its root relations.
-/

open scoped commutatorElement

namespace Quillen.FiniteRootLifting.LiteralGL5

/-- The literal finite matrix group used by this consumer. -/
abbrev G := Matrix.GeneralLinearGroup (Fin 5) ℚ

/-- Literal elementary matrices as homomorphisms from the additive rational group. -/
def sections (i j : Fin 5) (hij : i ≠ j) : Multiplicative ℚ →* G where
  toFun a := _root_.Quillen.ElementaryMatrix.unit i j hij a.toAdd
  map_one' := _root_.Quillen.ElementaryMatrix.unit_zero i j hij
  map_mul' a b := (_root_.Quillen.ElementaryMatrix.unit_mul_same i j hij a.toAdd b.toAdd).symm

/-- The identity projection has trivial, hence central, kernel. -/
lemma central_kernel : (MonoidHom.id G).ker ≤ Subgroup.center G := by
  intro g hg
  have hg' : g = 1 := hg
  simpa only [hg'] using (Subgroup.one_mem (Subgroup.center G))

/-- The sections project to the original elementary-matrix units coefficientwise. -/
lemma projection (i j : Fin 5) (hij : i ≠ j) (a : ℚ) :
    MonoidHom.id G (root sections i j hij a) = _root_.Quillen.ElementaryMatrix.unit i j hij a := rfl

/-- Every product-one weight tuple has its actual diagonal matrix as a covariant lift. -/
lemma covariance : DiagonalCovariance (MonoidHom.id G) sections := by
  intro w _
  refine ⟨diagonalUnit ℚ w, rfl, ?_⟩
  intro i j hij a
  exact diagonalUnit_conjugate_unit ℚ w i j hij a

/-- The generic endpoint is realized by these actual finite rational matrices. -/
lemma relations :
    (∀ (i j : Fin 5) (hij : i ≠ j) (a b : ℚ),
      _root_.Quillen.ElementaryMatrix.unit i j hij a * _root_.Quillen.ElementaryMatrix.unit i j hij
        b =
        _root_.Quillen.ElementaryMatrix.unit i j hij (a + b)) ∧
    (∀ (i j k l : Fin 5) (hij : i ≠ j) (hkl : k ≠ l)
        (_hjk : j ≠ k) (_hli : l ≠ i) (a b : ℚ),
      ⁅_root_.Quillen.ElementaryMatrix.unit i j hij a, _root_.Quillen.ElementaryMatrix.unit k l hkl
        b⁆ = 1) ∧
    (∀ (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : ℚ),
      ⁅_root_.Quillen.ElementaryMatrix.unit i j hij a, _root_.Quillen.ElementaryMatrix.unit j k hjk
        b⁆ =
        _root_.Quillen.ElementaryMatrix.unit i k hik (a * b)) :=
  original_root_relations (MonoidHom.id G) central_kernel sections
    projection covariance (by decide : 5 ≤ 5)

/-- Shared-row roots are covered by the original disjoint condition. -/
lemma shared_row (a b : ℚ) :
    ⁅_root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) a,
      _root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 2 (by decide) b⁆ = 1 := by
  exact relations.2.1 0 1 0 2 (by decide) (by decide) (by decide) (by decide) a b

/-- Shared-column roots are also covered. -/
lemma shared_column (a b : ℚ) :
    ⁅_root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 2 (by decide) a,
      _root_.Quillen.ElementaryMatrix.unit (1 : Fin 5) 2 (by decide) b⁆ = 1 := by
  exact relations.2.1 0 2 1 2 (by decide) (by decide) (by decide) (by decide) a b

/-- Identical roots are handled through the supplied additive homomorphism. -/
lemma identical_root (a b : ℚ) :
    ⁅_root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) a,
      _root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) b⁆ = 1 := by
  exact relations.2.1 0 1 0 1 (by decide) (by decide) (by decide) (by decide) a b

/-- The original ordered commutator has the positive literal coefficient `a * b`. -/
lemma ordered_chain (a b : ℚ) :
    ⁅_root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) a,
      _root_.Quillen.ElementaryMatrix.unit (1 : Fin 5) 2 (by decide) b⁆ =
        _root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 2 (by decide) (a * b) := by
  exact relations.2.2 0 1 2 (by decide) (by decide) (by decide) a b

/-- A concrete positive coefficient check for the ordered original word. -/
lemma ordered_chain_two_three :
    ⁅_root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) (2 : ℚ),
      _root_.Quillen.ElementaryMatrix.unit (1 : Fin 5) 2 (by decide) (3 : ℚ)⁆ =
        _root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 2 (by decide) (6 : ℚ) := by
  simpa only [show (2 : ℚ) * 3 = 6 by norm_num] using ordered_chain 2 3

/-- Root addition is consumed from the same conditional endpoint. -/
lemma root_addition (a b : ℚ) :
    _root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) a *
      _root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) b =
        _root_.Quillen.ElementaryMatrix.unit (0 : Fin 5) 1 (by decide) (a + b) := by
  exact relations.1 0 1 (by decide) a b

end Quillen.FiniteRootLifting.LiteralGL5

end
