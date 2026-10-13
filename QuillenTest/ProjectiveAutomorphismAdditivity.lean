/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Algebra.Category.ModuleCat.ProjectiveAutomorphismAdditivity

/-! Actual projective conjugation, complement independence, and direct-sum consumers. -/
open CategoryTheory CategoryTheory.Limits Quillen.RightMatrix
universe u
variable {R : Type u} [Ring R]

example (P Q : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    (g : Aut P) (h : Aut Q) :
    projectiveAutomorphismClass (P ⨿ Q) (coprod.mapIso g h) =
      projectiveAutomorphismClass P g * projectiveAutomorphismClass Q h :=
  projectiveAutomorphismClass_coprod P Q g h

example (P : ProjectiveMatrices R)
    (M : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    (e : imageFunctor.obj P ≅ M) (g : Aut P) :
    projectiveAutomorphismClass M (Aut.autMulEquivOfIso e (imageFunctor.mapIso g)) =
      automorphismClass P g := projectiveAutomorphismClass_presentation P M e g

example {P Q : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ}
    (i : P ⟶ Q) (r : Q ⟶ P) (hr : i ≫ r = 𝟙 P) (g : Aut P) (h : Aut Q)
    (hh : h.hom = r ≫ g.hom ≫ i + 𝟙 Q - r ≫ i) :
    projectiveAutomorphismClass Q h = projectiveAutomorphismClass P g :=
  projectiveAutomorphismClass_splitExtension i r hr g h hh
