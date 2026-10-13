/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveZeroFiberCompatibility

/-! # The zero-fiber equivalence preserves the original entry and its chosen structure map -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
namespace QuillenTest.ProjectiveZeroFiberCompatibility
variable (R : Type u) [Ring R]

example : completionZeroIsoFiberEntry R ⋙
    IsoFiber.forget (localizedExtensionProjection R) (exactStructure R).qZero =
      completionIdentityEntry R := by simp

example (X : GroupCompletionCategory R) :
    (IsoFiber.structureIso (localizedExtensionProjection R) (exactStructure R).qZero).hom.app
        ((completionZeroIsoFiberEntry R).obj X) =
      (completionIdentityProjectionIsoZero R).inv.app X :=
  completionZeroIsoFiberEntry_structure R X

end QuillenTest.ProjectiveZeroFiberCompatibility
