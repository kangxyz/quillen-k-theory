/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeFree
import Mathlib.Algebra.Ring.PUnit

/-! The actual free-module identification retains the original matrix and stable actions. -/

noncomputable section
universe u v
open CategoryTheory Quillen Quillen.RightMatrix Quillen.FiniteProjectiveModule
variable {R : Type u} {S : Type v} [Ring R] [Ring S]

example (f : R →+* S) (n : ℕ) :
    (rightBaseChange f).obj (free (R := Rᵐᵒᵖ) n) ≅ free (R := Sᵐᵒᵖ) n :=
  freeBaseChangeIso f n

example (f : R →+* S) (n : ℕ) (g : StableGeneralLinear.GL R n) :
    (rightBaseChange f).map (freeAutEquiv R n g).hom ≫ (freeBaseChangeIso f n).hom =
      (freeBaseChangeIso f n).hom ≫ (freeAutEquiv S n (StableGeneralLinear.finiteMap f n g)).hom :=
  freeBaseChangeIso_matrix_action f n g

example (f : R →+* S) (n : ℕ) (g : StableGeneralLinear.GL R n) :
    (rightBaseChange f).map (freeAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom ≫
        (freeBaseChangeIso f (n + 1)).hom =
      (freeBaseChangeIso f (n + 1)).hom ≫
        (freeAutEquiv S (n + 1)
          (StableGeneralLinear.step S n (StableGeneralLinear.finiteMap f n g))).hom :=
  freeBaseChangeIso_step_action f n g

example : (rightBaseChange (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))).obj
    (free (R := (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ) 2) ≅
      free (R := (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ) 2 := freeBaseChangeIso _ _

example : (rightBaseChange (RingHom.id PUnit)).obj (free (R := PUnitᵐᵒᵖ) 0) ≅
    free (R := PUnitᵐᵒᵖ) 0 := freeBaseChangeIso _ _
