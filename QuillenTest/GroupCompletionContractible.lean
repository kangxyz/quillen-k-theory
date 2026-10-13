/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.GroupCompletionContractible

/-! # QuillenTest for the non-circular contraction of Grayson's total localization -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory Quillen Quillen.GroupCompletion
namespace QuillenTest.GroupCompletionContractible
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [MonoidalCategory C] [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  [MonoidalLeftAction C D] [ContractibleSpace (ClassifyingSpace D)]

example : ContractibleSpace (ClassifyingSpace (Localization C D)) :=
  Localization.classifyingSpace_contractible

example :
    (Localization.projectionClassifyingHomotopyEquiv (C := C) (D := D)).toFun =
      (classifyingSpaceMap Localization.projection).hom := rfl

example (B : C) :
    (Localization.commaClassifyingHomotopyEquiv (D := D) B).invFun =
      (classifyingSpaceMap (Localization.commaEntry B)).hom := rfl

example (B : C) : Localization.commaTransport (D := D) B ⊣ Localization.commaEntry B :=
  Localization.commaTransportAdjunction B

end QuillenTest.GroupCompletionContractible
