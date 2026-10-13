/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveExtensionLocalization

/-! # The actual finite-projective localized total space is contractible -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
namespace QuillenTest.ProjectiveExtensionLocalization
attribute [local instance] directSumMonoidal
variable (R : Type u) [Ring R]

example : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
  localizedExtension_classifyingSpace_contractible R

example (A : IsoCategory R) (x : (exactStructure R).ExtensionTotal) :
    (localizedExtensionBaseProjection R).obj (localizedExtensionPair R A x) = ⟨A⟩ := rfl

example : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory ℤ)) :=
  localizedExtension_classifyingSpace_contractible ℤ

end QuillenTest.ProjectiveExtensionLocalization
