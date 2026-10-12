/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionFiberFormula
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers for the full original completion-to-fiber formula

These examples test arbitrary realization points and the entire path parameter,
including opposite noncommutative rings and the zero ring. The direct-inverse
comparison retains the original source coordinate and the actual relative
homotopy of the stored paths.
-/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
universe u
variable (R : Type u) [Ring R]

example : completionToOriginalQHomotopyFiber R =
    HomotopyFiber.lift (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint (exactStructure R).qZero)
      (classifyingSpaceMapUniversal (completionIdentityEntry R))
      (completionInverseNullhomotopy R) :=
  completionToOriginalQHomotopyFiber_eq_inverseLift R

example (x : ClassifyingSpace (GroupCompletionCategory R)) :
    (completionToOriginalQHomotopyFiber R x).1.1 =
      classifyingSpaceMapUniversal (completionIdentityEntry R) x :=
  completionToOriginalQHomotopyFiber_source R x

example (x : ClassifyingSpace (GroupCompletionCategory R)) (t : unitInterval) :
    (completionToOriginalQHomotopyFiber R x).1.2 t =
      classifyingSpaceUniversalHomotopy (completionIdentityProjectionIsoZero R).inv
        (unitInterval.symm t, x) :=
  completionToOriginalQHomotopyFiber_path R x t

example :
    (HomotopyFiber.lift (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint (exactStructure R).qZero)
      (classifyingSpaceMapUniversal (completionIdentityEntry R))
      (completionDirectNullhomotopy R)).Homotopy
        (completionToOriginalQHomotopyFiber R) :=
  completionDirectInverseLiftHomotopy R

example (s : unitInterval) (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    (completionDirectInverseLiftHomotopy Rᵐᵒᵖ (s, x)).1.1 =
      classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ) x :=
  completionDirectInverseLiftHomotopy_source Rᵐᵒᵖ s x

example (s t : unitInterval) (x : ClassifyingSpace (GroupCompletionCategory R)) :
    (completionDirectInverseLiftHomotopy R (s, x)).1.2 t =
      completionDirectInverseNullhomotopyHomotopy R (s, (t, x)) :=
  completionDirectInverseLiftHomotopy_path R s t x

example (x : ClassifyingSpace (GroupCompletionCategory (ZMod 1))) (t : unitInterval) :
    (completionToOriginalQHomotopyFiber (ZMod 1) x).1.2 t =
      classifyingSpaceUniversalHomotopy
        (completionIdentityProjectionIsoZero (ZMod 1)).inv (unitInterval.symm t, x) :=
  completionToOriginalQHomotopyFiber_path (ZMod 1) x t

example (s : unitInterval) (x : ClassifyingSpace (GroupCompletionCategory (ZMod 1))) :
    (completionDirectInverseLiftHomotopy (ZMod 1) (s, x)).1.1 =
      classifyingSpaceMapUniversal (completionIdentityEntry (ZMod 1)) x :=
  completionDirectInverseLiftHomotopy_source (ZMod 1) s x
