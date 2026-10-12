/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Algebra.Group.StableQuotientInvariance
import Mathlib.Algebra.Ring.PUnit

/-! Consumer checks for stable classes without commutativity or invariant basis number. -/
open Quillen.StableGeneralLinear
universe u
variable (R : Type u) [Ring R]

example (n m : ℕ) (g : GL R n) (h : GL R m) :
    finiteClass R (n + m) (Quillen.ElementaryMatrix.reindex finSumFinEquiv
      (Quillen.ElementaryMatrix.blockSum g h)) = finiteClass R n g * finiteClass R m h :=
  finiteClass_blockSum R n m g h

example {n m : ℕ} (g : GL R n) (h : GL R m)
    (a : Matrix (Fin n) (Fin m) R) (b : Matrix (Fin m) (Fin n) R)
    (hab : a * b = 1) (hba : b * a = 1) (hc : a * h.val = g.val * a) :
    finiteClass R n g = finiteClass R m h :=
  finiteClass_rectangular_conjugate R g h a b hab hba hc

example (g : GL PUnit 0) (h : GL PUnit 1) :
    finiteClass PUnit 0 g = finiteClass PUnit 1 h :=
  finiteClass_rectangular_conjugate PUnit g h 0 0
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
