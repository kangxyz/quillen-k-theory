/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.LinearAlgebra.Matrix.GeneralLinearGroup.BlockOperations
public import Quillen.Algebra.Group.StableElementaryQuotient

/-!
# Stable quotient invariance under bases and block sums

These identities concern the actual stable elementary quotient over any ring.
They retain finite ranks as labels and do not assume invariant basis number.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w x
namespace Quillen.StableGeneralLinear
variable (R : Type u) [Ring R]

/-- The original finite-stage matrix class in the stable elementary quotient. -/
def finiteClass (n : ℕ) : GL R n →* ElementaryQuotient R :=
  (quotientMap R).comp (of R n)

/-- Inner changes of basis do not change the original finite matrix class. -/
lemma finiteClass_conjugate (n : ℕ) (g p : GL R n) :
    finiteClass R n (p * g * p⁻¹) = finiteClass R n g := by
  simp [map_mul, map_inv, mul_comm]

/-- Appending an identity block does not change the finite matrix class. -/
lemma finiteClass_transition {n m : ℕ} (h : n ≤ m) (g : GL R n) :
    finiteClass R m (transition R n m h g) = finiteClass R n g := by
  change quotientMap R (of R m (transition R n m h g)) = _
  rw [of_transition]
  rfl

/-- Permuting a labelled finite basis leaves its actual stable quotient class unchanged. -/
lemma finiteClass_reindex (n : ℕ) (e : Fin n ≃ Fin n) (g : GL R n) :
    finiteClass R n (ElementaryMatrix.reindex e g) = finiteClass R n g := by
  rw [reindex_eq_conjugate, finiteClass_conjugate]

/-- The class is independent of enumerations of the same finite coordinate set. -/
lemma finiteClass_enumeration {I : Type v} [Fintype I] [DecidableEq I]
    {n m : ℕ} (e : I ≃ Fin n) (f : I ≃ Fin m) (g : (Matrix I I R)ˣ) :
    finiteClass R n (ElementaryMatrix.reindex e g) =
      finiteClass R m (ElementaryMatrix.reindex f g) := by
  have hn : n = m := by
    simpa using Fintype.card_congr (e.symm.trans f)
  subst m
  have h := finiteClass_reindex R n (e.symm.trans f) (ElementaryMatrix.reindex e g)
  rw [reindex_trans] at h
  have he : e.trans (e.symm.trans f) = f := by ext i; simp
  rw [he] at h
  exact h.symm

/-- The class of a block matrix with an identity right block is the original class. -/
lemma finiteClass_blockSum_one (n m : ℕ) (g : GL R n) :
    finiteClass R (n + m) (ElementaryMatrix.reindex finSumFinEquiv
      (ElementaryMatrix.blockSum g (1 : GL R m))) = finiteClass R n g := by
  rw [← transition_eq_reindex_blockSum]
  exact finiteClass_transition R _ g

/-- Appending an identity on the left also preserves the original stable quotient class. -/
lemma finiteClass_one_blockSum (n m : ℕ) (g : GL R n) :
    finiteClass R (m + n) (ElementaryMatrix.reindex finSumFinEquiv
      (ElementaryMatrix.blockSum (1 : GL R m) g)) = finiteClass R n g := by
  rw [← reindex_blockSum_swap R g (1 : GL R m), reindex_trans]
  exact (finiteClass_enumeration R
    ((Equiv.sumComm (Fin n) (Fin m)).trans finSumFinEquiv)
    finSumFinEquiv (ElementaryMatrix.blockSum g (1 : GL R m))).trans
      (finiteClass_blockSum_one R n m g)

/-- The original stable quotient converts block direct sum to multiplication. -/
lemma finiteClass_blockSum (n m : ℕ) (g : GL R n) (h : GL R m) :
    finiteClass R (n + m) (ElementaryMatrix.reindex finSumFinEquiv
      (ElementaryMatrix.blockSum g h)) = finiteClass R n g * finiteClass R m h := by
  have hb : ElementaryMatrix.blockSum g h =
      ElementaryMatrix.blockSum g (1 : GL R m) *
        ElementaryMatrix.blockSum (1 : GL R n) h := by
    rw [← ElementaryMatrix.blockSum_mul, mul_one, one_mul]
  rw [hb, map_mul, map_mul, finiteClass_blockSum_one, finiteClass_one_blockSum]

/-- Isomorphic free modules give the same automorphism class, even with unequal rank labels. -/
theorem finiteClass_rectangular_conjugate {n m : ℕ}
    (g : GL R n) (h : GL R m)
    (a : Matrix (Fin n) (Fin m) R) (b : Matrix (Fin m) (Fin n) R)
    (hab : a * b = 1) (hba : b * a = 1) (hconj : a * h.val = g.val * a) :
    finiteClass R n g = finiteClass R m h := by
  let w := rectangularSwap R a b hab hba
  have hw : w * ElementaryMatrix.blockSum (1 : GL R n) h =
      ElementaryMatrix.blockSum g (1 : GL R m) * w := by
    apply Units.ext
    change Matrix.fromBlocks 0 a b 0 * Matrix.fromBlocks 1 0 0 h.val =
      Matrix.fromBlocks g.val 0 0 1 * Matrix.fromBlocks 0 a b 0
    simp [Matrix.fromBlocks_multiply, hconj]
  let c := (finiteClass R (n + m)).comp
    (ElementaryMatrix.reindex (finSumFinEquiv (m := n) (n := m))).toMonoidHom
  have hc := congrArg c hw
  change c (w * ElementaryMatrix.blockSum (1 : GL R n) h) =
    c (ElementaryMatrix.blockSum g (1 : GL R m) * w) at hc
  rw [map_mul, map_mul] at hc
  have hh : c (ElementaryMatrix.blockSum (1 : GL R n) h) = finiteClass R m h :=
    finiteClass_one_blockSum R m n h
  have hg : c (ElementaryMatrix.blockSum g (1 : GL R m)) = finiteClass R n g :=
    finiteClass_blockSum_one R n m g
  rw [hh, hg, mul_comm (finiteClass R n g)] at hc
  exact (mul_left_cancel hc).symm

end Quillen.StableGeneralLinear
