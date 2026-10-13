/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.KTheory.Map.RightBaseChangeTensor
import Quillen.Algebra.Category.ModuleCat.MatrixImageTensor

/-! Regression properties of the literal tensor functor and original K-map comparison. -/

noncomputable section

universe u v w z a

open CategoryTheory MulOpposite Quillen
open Quillen.RightScalarExtension Quillen.FiniteProjectiveModule

section IndependentUniverses

variable {R : Type u} {S : Type v} {T : Type z} {U : Type a}
variable [Ring R] [Ring S] [Ring T] [Ring U]
variable (f : R →+* S) (g : S →+* T) (h : T →+* U)
variable {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M]

example (m : M) (s : S) (t : T) (q : U) :
    compEquiv (g.comp f) h
        (pure h (compEquiv f g (pure g (pure f m s) t)) q) =
      pure (h.comp (g.comp f)) m (h (g s) * (h t * q)) := by
  simp [mul_assoc]

example :
    (compEquiv (g.comp f) h (M := M)).toLinearMap.comp
        (RightScalarExtension.map h (compEquiv f g).toLinearMap) =
      (compEquiv f (h.comp g) (M := M)).toLinearMap.comp
        (compEquiv g h (M := Tensor f M)).toLinearMap :=
  compEquiv_assoc f g h

example (P : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :
    Module.Finite Sᵐᵒᵖ (Tensor f P.obj) ∧ Module.Projective Sᵐᵒᵖ (Tensor f P.obj) :=
  ⟨inferInstance, inferInstance⟩

example (P : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) (p : P.obj) (s : S) :
    (rightTensorBaseChangeEquiv f P).symm (op s • rightBaseChangeUnit f P p) =
      pure f p s := by
  rw [← rightTensorBaseChangeEquiv_pure, LinearEquiv.symm_apply_apply]

example (P : RightMatrix.ProjectiveMatrices R)
    (y : (RightMatrix.linearMap (P.p.map f)).range) :
    RightMatrix.tensorImageEquiv f P
      (∑ i, pure f (RightMatrix.imageColumn P i) (y.val i)) = y := by
  rw [← RightMatrix.tensorImageEquiv_symm_apply, LinearEquiv.apply_symm_apply]

example {P Q : RightMatrix.ProjectiveMatrices R} (a : P ⟶ Q)
    (x : Tensor f (RightMatrix.linearMap P.p).range) :
    RightMatrix.tensorImageEquiv f Q
        (RightScalarExtension.map f (RightMatrix.imageMap a) x) =
      RightMatrix.imageMap ((RightMatrix.baseChange f).map a)
        (RightMatrix.tensorImageEquiv f P x) :=
  DFunLike.congr_fun (RightMatrix.tensorImageEquiv_naturality f a) x

end IndependentUniverses

section OriginalKMap

variable {R S : Type u} [Ring R] [Ring S]

example (f : R →+* S) (n : ℕ) (x : (exactStructure Rᵐᵒᵖ).K n) :
    (rightTensorBaseChangeExact f).KMap n x = (rightBaseChangeExact f).KMap n x := by
  rw [rightTensorBaseChangeExact_KMap]

end OriginalKMap
