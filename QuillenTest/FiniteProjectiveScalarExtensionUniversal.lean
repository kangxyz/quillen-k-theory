/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal

/-! Arbitrary ambient targets test the actual scalar-extension universal property. -/
noncomputable section
open CategoryTheory Quillen.FiniteProjectiveModule
universe u v w
variable {R : Type u} {S : Type v} [Ring R] [Ring S]

example (f : R →+* S) (P : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ)
    (h : P.obj →ₛₗ[f.op] N) :
    (rightBaseChangeLift f P N h).comp (rightBaseChangeUnit f P) = h :=
  rightBaseChangeLift_unit f P N h

example (f : R →+* S) {P Q : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ} (g : P ⟶ Q)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : ((rightBaseChange f).obj Q).obj →ₗ[Sᵐᵒᵖ] N) :
    rightBaseChangeHomEquiv f P N (h.comp ((rightBaseChange f).map g).hom.hom) =
      (rightBaseChangeHomEquiv f Q N h).comp g.hom.hom :=
  rightBaseChangeHomEquiv_naturality_source f g N h

example {T : Type u} [Ring T] (f : R →+* T)
    (P : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{u} Tᵐᵒᵖ) :
    (((rightBaseChange f).obj P).obj ⟶ N) ≃+
      (P.obj ⟶ (ModuleCat.restrictScalars f.op).obj N) :=
  rightBaseChangeModuleHomEquiv f P N
