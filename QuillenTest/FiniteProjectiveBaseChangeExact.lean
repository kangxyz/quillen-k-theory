/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
import Mathlib.Algebra.Ring.PUnit

/-! Actual change of rings preserves sums and all inherited conflations. -/

noncomputable section
universe u v
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
variable {R : Type u} {S : Type v} [Ring R] [Ring S]

example (f : R →+* S) {P Q : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ}
    (a b : P ⟶ Q) : (rightBaseChange f).map (a + b) =
      (rightBaseChange f).map a + (rightBaseChange f).map b := Functor.map_add _

example (f : R →+* S) (K : ShortComplex (Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ))
    (hK : (exactStructure Rᵐᵒᵖ).conflation K) :
    (exactStructure Sᵐᵒᵖ).conflation (K.map (rightBaseChange f)) :=
  (rightBaseChangeExact f).map_conflation K hK

example (f : R →+* S) (P : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :
    (rightBaseChangeExact f).mapQ.obj
      (Q.of (exactStructure Rᵐᵒᵖ).deflation (exactStructure Rᵐᵒᵖ).inflation P) =
    Q.of (exactStructure Sᵐᵒᵖ).deflation (exactStructure Sᵐᵒᵖ).inflation
      ((rightBaseChange f).obj P) := (rightBaseChangeExact f).mapQ_obj_of P

example : (rightBaseChange (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))).Additive := inferInstance
example : (rightBaseChange (RingHom.id PUnit)).Additive := inferInstance
