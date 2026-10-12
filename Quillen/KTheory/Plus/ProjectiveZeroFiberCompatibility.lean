/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveZeroFiberEquivalence
public import Quillen.CategoryTheory.IsoFiberStructureMap

/-! # Compatibility of the original zero-fiber entry with the total projection -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace Quillen.FiniteProjectiveModule
variable (R : Type u) [Ring R]

/-- The zero-fiber entry forgets to the original identity-extension entry exactly. -/
@[simp]
lemma completionZeroIsoFiberEntry_forget :
    completionZeroIsoFiberEntry R ⋙
      IsoFiber.forget (localizedExtensionProjection R) (exactStructure R).qZero =
        completionIdentityEntry R := rfl

/-- The actual structure path starts with the inverse of the original canonical
identity-quotient comparison, including at the monoidal unit. -/
lemma completionZeroIsoFiberEntry_structure (X : GroupCompletionCategory R) :
    (IsoFiber.structureIso (localizedExtensionProjection R) (exactStructure R).qZero).hom.app
        ((completionZeroIsoFiberEntry R).obj X) =
      (completionIdentityProjectionIsoZero R).inv.app X := rfl

end Quillen.FiniteProjectiveModule
