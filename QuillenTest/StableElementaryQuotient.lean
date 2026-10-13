/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Algebra.Group.StableElementaryQuotient
import Mathlib.Algebra.Ring.PUnit

/-! The quotient keeps its original projection, elementary kernel, and ring maps. -/

open Quillen.StableGeneralLinear

noncomputable section

variable {R : Type*} [Ring R]

example : CommGroup (ElementaryQuotient R) := inferInstance

example : (quotientMap R).ker = elementary R := ker_quotientMap R

example (g : Quillen.StableGeneralLinear.Group R) :
    quotientEquivAbelianization R (quotientMap R g) = Abelianization.of g :=
  quotientEquivAbelianization_quotientMap R g

example (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R) :
    quotientMap R (of R n (Quillen.ElementaryMatrix.unit i j hij a)) = 1 :=
  (quotientMap_eq_one R _).mpr (unit_mem_elementary R n i j hij a)

example {S : Type*} [Ring S] (f : R →+* S) :
    (quotientRingMap f).comp (quotientMap R) = (quotientMap S).comp (map f) :=
  quotientMap_naturality f

example {S T : Type*} [Ring S] [Ring T] (f : R →+* S) (g : S →+* T) :
    quotientRingMap (g.comp f) = (quotientRingMap g).comp (quotientRingMap f) :=
  quotientRingMap_comp f g

example : CommGroup (ElementaryQuotient (Matrix (Fin 2) (Fin 2) ℤ)) := inferInstance

example : CommGroup (ElementaryQuotient PUnit) := inferInstance

example {H : Type*} [CommGroup H] (f : Quillen.StableGeneralLinear.Group R →* H) :
    (quotientLift R f).comp (quotientMap R) = f := by
  apply MonoidHom.ext
  intro g
  exact quotientLift_quotientMap R f g
