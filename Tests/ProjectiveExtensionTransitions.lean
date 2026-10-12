/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Topology.ClassifyingSpace.ProjectiveExtensionTransitions
public import Mathlib.Data.ZMod.Basic

/-! # Original contravariant Q transitions and universal comparison consumers -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction

example (R : Type u) [Ring R] :
    TheoremB.StructuredTransitionWeakEquivalencesUniversal (localizedExtensionProjection R) :=
  localizedExtensionProjection_structuredWeakTransitions R

example (R : Type u) [Ring R]
    (b : Q (exactStructure R).deflation (exactStructure R).inflation) :
    IsWeakHomotopyEquivalence (TheoremB.structuredFiberComparisonUniversal
      (localizedExtensionProjection R) b) :=
  localizedExtensionProjection_structuredComparison_isWeakHomotopyEquivalence R b

example : TheoremB.StructuredTransitionWeakEquivalencesUniversal
    (localizedExtensionProjection (ZMod 1)) :=
  localizedExtensionProjection_structuredWeakTransitions (ZMod 1)

example (R : Type u) [Ring R]
    {X Y : Quillen.FiniteProjectiveModule.Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    (U : LocalizedFixedExtensionCategory R Y) :
    ((localizedFixedExtensionSpanComma R s).app U).right =
      localizedExtensionOriginalHom R U.obj.1
        ((exactStructure R).extensionDeflationSpanHom s U.obj.2) := rfl
