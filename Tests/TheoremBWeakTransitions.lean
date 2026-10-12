/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremB.WeakTransitionComparison

/-! # Consumers of the canonical weak-transition comparisons -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

example (h : TransitionHomotopyEquivalences F) : TransitionWeakEquivalences F := by
  intro d e f
  exact isWeakHomotopyEquivalence_of_homotopyEquiv (transitionHomotopyEquiv F h f)

example (h : StructuredTransitionHomotopyEquivalences F) :
    StructuredTransitionWeakEquivalences F := by
  intro d e f
  exact isWeakHomotopyEquivalence_of_homotopyEquiv (structuredTransitionHomotopyEquiv F h f)

example (h : TransitionWeakEquivalences F) (c : C) (n : ℕ) :
    ↑(fiberComparisonPiEquivOfWeakTransitions F h c n) =
      piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c) := rfl

example (h : StructuredTransitionWeakEquivalences F) (c : C) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c)) :=
  structuredFiberComparison_bijective_of_weakTransitions F h c 0
end Quillen.TheoremB
