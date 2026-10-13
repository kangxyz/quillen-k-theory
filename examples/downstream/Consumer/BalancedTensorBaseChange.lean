/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Map.RightBaseChangeTensor
public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveTensorCoherence
public import Quillen.Algebra.Category.ModuleCat.MatrixImageTensor

/-!
A downstream consumer of the actual universe-lifted naturality square and the
common-universe equality of original, normalized K-maps.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Quillen
open Quillen.RightScalarExtension Quillen.FiniteProjectiveModule

namespace BalancedTensorBaseChangeConsumer

section MixedUniverses

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (f : R →+* S)
variable {P Q : FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ}

/-- Naturality uses the actual lifted original functor for all source maps and tensor elements. -/
theorem lifted_square (a : P ⟶ Q) (x : Tensor f P.obj) :
    ULift.up (rightTensorBaseChangeEquiv f Q (RightScalarExtension.map f a.hom.hom x)) =
      (ModuleCat.uliftFunctor.{u} Sᵐᵒᵖ).map
        ((property Sᵐᵒᵖ).ι.map ((rightBaseChange f).map a))
        (ULift.up (rightTensorBaseChangeEquiv f P x)) := by
  exact congrArg
    (fun k : ((rightTensorBaseChange f).obj P).obj ⟶
      (ModuleCat.uliftFunctor.{u} Sᵐᵒᵖ).obj (((rightBaseChange f).obj Q).obj) => k x)
    ((rightTensorBaseChangeLiftedIso f).hom.naturality a)

/-- A rectangular matrix acts compatibly on the actual quotient and mapped image. -/
theorem rectangular_square {A B : RightMatrix.ProjectiveMatrices R} (a : A ⟶ B)
    (x : Tensor f (RightMatrix.linearMap A.p).range) :
    RightMatrix.tensorImageEquiv f B
        (RightScalarExtension.map f (RightMatrix.imageMap a) x) =
      RightMatrix.imageMap ((RightMatrix.baseChange f).map a)
        (RightMatrix.tensorImageEquiv f A x) :=
  DFunLike.congr_fun (RightMatrix.tensorImageEquiv_naturality f a) x

/-- The tensor identification respects the pre-existing composition isomorphism. -/
theorem original_composition_square {T : Type w} [Ring T] (g : S →+* T)
    (x : Tensor g (Tensor f P.obj)) :
    rightTensorBaseChangeEquiv (g.comp f) P (compEquiv f g x) =
      ((rightBaseChangeComp f g).hom.app P).hom.hom
        (rightTensorBaseChangeEquiv g ((rightBaseChange f).obj P)
          (RightScalarExtension.map g (rightTensorBaseChangeEquiv f P).toLinearMap x)) :=
  DFunLike.congr_fun (rightTensorBaseChangeEquiv_comp f g P) x

end MixedUniverses

section SameUniverse

variable {R S : Type u} [Ring R] [Ring S]

/-- A client can replace the tensor K-map by the original map at every K-degree. -/
theorem tensor_KMap_original (f : R →+* S) (n : ℕ)
    (x : (exactStructure Rᵐᵒᵖ).K n) :
    (rightTensorBaseChangeExact f).KMap n x = (rightBaseChangeExact f).KMap n x := by
  rw [rightTensorBaseChangeExact_KMap]

end SameUniverse

end BalancedTensorBaseChangeConsumer
