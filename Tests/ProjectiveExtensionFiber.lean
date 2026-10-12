/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.ProjectiveExtensionFiber

/-! # Contractibility of the original fixed-quotient extension action model -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace Quillen.FiniteProjectiveModule
variable (R : Type u) [Ring R]
attribute [local instance] directSumMonoidal extensionFiberDirectSumAction

example (C : Category.{u, u} R) : IsConnected (ExtensionActionCategory R C) :=
  extensionActionCategory_isConnected R C

example (C : Category.{u, u} R) (n : ℕ) :
    Subsingleton (ShiftedHomotopyGroup (ExtensionActionCategory R C) (extensionActionUnit R C) n) :=
  extensionAction_unitPi_subsingleton R C n

example (C : Category.{u, u} R) : IsWeakHomotopyEquivalence
    (ContinuousMap.const (ClassifyingSpace (ExtensionActionCategory R C))
      (PUnit.unit : PUnit.{u + 2})) := extensionAction_weaklyContractible R C

example (C : Category.{u, u} R) :
    (extensionActionDiagonalNatTrans R C).app (extensionActionUnit R C) =
      (extensionActionLeftUnit R C).inv.app (extensionActionUnit R C) :=
  extensionAction_diagonal_unit R C

example (C : Category.{u, u} R) :
    (extensionActionLeftUnit R C).hom.app (extensionActionUnit R C) =
      (extensionActionRightUnit R C).hom.app (extensionActionUnit R C) :=
  extensionAction_unit_coherence R C

end Quillen.FiniteProjectiveModule
