/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Algebra.Matrix.IdempotentAutomorphismClass

/-! Consumer checks for actual idempotent-presentation invariance. -/
open CategoryTheory CategoryTheory.Idempotents Quillen.RightMatrix
universe u
variable {R : Type u} [Ring R]

example {P Q : ProjectiveMatrices R} (e : P ≅ Q) (g : Aut P) :
    automorphismClass Q (Aut.autMulEquivOfIso e g) = automorphismClass P g :=
  automorphismClass_conjugate e g

example (n : ℕ) (g : Quillen.StableGeneralLinear.GL R n) :
    automorphismClass ((toKaroubi (FreeCategory R)).obj ⟨n⟩) (matrixUnitAut n g) =
      Quillen.StableGeneralLinear.finiteClass R n g := automorphismClass_matrixUnitAut n g

example {P Q : ProjectiveMatrices R} (e : P ≅ Q) (g : Aut P) (h : Aut Q)
    (hc : e.inv ≫ g.hom = h.hom ≫ e.inv) :
    automorphismClass P g = automorphismClass Q h :=
  automorphismClass_presentation e g h hc
