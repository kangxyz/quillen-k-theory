/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.ClassifyingSpace.ProjectiveCompletionLoops
public import Mathlib.Data.ZMod.Basic

/-! # Original Q-loop comparison with its displayed basepoint track -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Quillen Quillen.FiniteProjectiveModule

example (R : Type u) [Ring R] (U : GroupCompletionCategory R) :
    IsWeakHomotopyEquivalence (completionToOriginalQLoops R U) :=
  completionToOriginalQLoops_isWeakHomotopyEquivalence R U

example (U : GroupCompletionCategory (ZMod 1)) :
    IsWeakHomotopyEquivalence (completionToOriginalQLoops (ZMod 1) U) :=
  completionToOriginalQLoops_isWeakHomotopyEquivalence (ZMod 1) U

example (R : Type u) [Ring R] (U : GroupCompletionCategory R) :
    Path (completionToOriginalQLoops R U (classifyingSpacePoint U))
      (Path.refl (classifyingSpacePoint (exactStructure R).qZero)) :=
  completionToOriginalQLoopsBasepointPath R U

example (R : Type u) [Ring R] (U : GroupCompletionCategory R) (t : unitInterval) :
    (completionToOriginalQHomotopyFiber R (classifyingSpacePoint U)).1.2 t =
      classifyingSpacePath ((completionIdentityProjectionIsoZero R).inv.app U)
        (unitInterval.symm t) :=
  completionToOriginalQHomotopyFiber_vertex_path R U t
