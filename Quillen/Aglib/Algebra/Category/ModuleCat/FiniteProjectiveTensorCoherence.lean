/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeTensor
public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUnitCoherence

/-!
# Coherence with the original change-of-rings comparisons

The canonical tensor identification intertwines the literal tensor identity and
composition equivalences with the unchanged original `rightBaseChangeId` and
`rightBaseChangeComp`. The proof uses the actual original units; no replacement
identity or composition comparison is chosen. Ring universes are independent.
-/

@[expose] public section

open Quillen.RightScalarExtension


noncomputable section

universe u v w

namespace Quillen.FiniteProjectiveModule

open RightScalarExtension

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- The canonical tensor identification respects the original identity comparison. -/
theorem rightTensorBaseChangeEquiv_id (P : Category.{u, u} Rᵐᵒᵖ) :
    ((rightBaseChangeId (R := R)).hom.app P).hom.hom.comp
        (rightTensorBaseChangeEquiv (RingHom.id R) P).toLinearMap =
      (idEquiv (M := P.obj)).toLinearMap := by
  apply hom_ext_unit (RingHom.id R)
  intro p
  simpa using rightBaseChangeId_hom_unit P p

/-- The canonical tensor identification respects the original composition comparison. -/
theorem rightTensorBaseChangeEquiv_comp (f : R →+* S) (g : S →+* T)
    (P : Category.{u, u} Rᵐᵒᵖ) :
    (rightTensorBaseChangeEquiv (g.comp f) P).toLinearMap.comp
        (compEquiv f g (M := P.obj)).toLinearMap =
      ((rightBaseChangeComp f g).hom.app P).hom.hom.comp
        ((rightTensorBaseChangeEquiv g ((rightBaseChange f).obj P)).toLinearMap.comp
          (RightScalarExtension.map g (rightTensorBaseChangeEquiv f P).toLinearMap)) := by
  apply hom_ext_unit_unit f g
  intro p
  simpa using (rightBaseChangeComp_hom_unit f g P p).symm

end Quillen.FiniteProjectiveModule
