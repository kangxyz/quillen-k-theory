/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.ProjectiveZeroFiber

/-! # Tests for the actual zero isomorphism fiber and its retained original map -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
namespace Tests.ProjectiveZeroFiber
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
  extensionDirectSumAction identityExtensionLinear identityExtensionPairLinear

example (A B : IsoCategory R) :
    ((completionZeroIsoFiberEntry R).obj (completionPair R A B)).obj.hom =
      ((exactStructure R).identityProjectionIsoZero B.of).inv := rfl

example (A B : IsoCategory R) :
    ((completionZeroIsoFiberEntry R).obj (completionPair R A B)).obj.right =
      localizedExtensionPair R A ((exactStructure R).identityExtension B.of) := rfl

example : (completionZeroIsoFiberEntry R).Full := inferInstance
example : (completionZeroIsoFiberEntry R).Faithful := inferInstance
example : (completionZeroIsoFiberEntry R).EssSurj := inferInstance

example : (completionZeroIsoFiberClassifyingHomotopyEquiv R).toFun =
    classifyingSpaceMapUniversal (completionZeroIsoFiberEntry R) := by simp

example : GroupCompletionCategory ℤ ≌ ZeroIsoFiber ℤ :=
  completionZeroIsoFiberEquivalence ℤ

end Tests.ProjectiveZeroFiber
