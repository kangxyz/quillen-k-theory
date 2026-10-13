/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Algebra.Matrix.ElementaryReindex

/-! Reindexing preserves actual elementary generators and their generated subgroup. -/

open Quillen.ElementaryMatrix

variable {R : Type*} [Ring R]

example :
    (subgroup (Fin 2 ⊕ Fin 3) R).map (reindex finSumFinEquiv).toMonoidHom =
      subgroup (Fin 5) R :=
  reindex_subgroup finSumFinEquiv

example (a : R) :
    reindex (Equiv.swap (0 : Fin 3) 2) (unit (0 : Fin 3) 1 (by decide) a) =
      unit (2 : Fin 3) 1 (by decide) a := by
  rw [reindex_unit]
  simp only [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 by decide,
    show (Equiv.swap (0 : Fin 3) 2) 1 = 1 by decide]
