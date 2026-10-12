/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Plus.ProjectiveCompletionZerothHomotopy

/-! # Genuine completion path components and the unchanged K₀ -/

noncomputable section

open Quillen Quillen.FiniteProjectiveModule

universe u

variable {R S : Type u} [Ring R] [Ring S]

-- Equality of the original K₀ labels detects paths between arbitrary realization points.
example (x y : ClassifyingSpace (GroupCompletionCategory R)) :
    completionZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk x) =
      completionZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk y) ↔ Joined x y := by
  rw [(completionZerothHomotopyKZeroEquiv R).injective.eq_iff]
  exact Quotient.eq

-- Every original homotopical K₀ class comes from an actual completion object vertex.
example (k : (exactStructure R).K 0) :
    ∃ X : GroupCompletionCategory R, completionKZeroClass R X = k := by
  obtain ⟨a, ha⟩ := (completionZerothHomotopyKZeroEquiv R).surjective k
  obtain ⟨X, rfl⟩ := classifyingSpaceVertexComponent_surjective (GroupCompletionCategory R) a
  exact ⟨X, (completionZerothHomotopyKZeroEquiv_point R X).symm.trans ha⟩

-- Naturality applies to every actual realization point, without selecting a replacement vertex.
example (f : R →+* S) (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    (rightBaseChangeExact f).KMap 0
      (completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ (ZerothHomotopy.mk x)) =
    completionZerothHomotopyKZeroEquiv Sᵐᵒᵖ
      (ZerothHomotopy.mk (completionBaseChangeMap f x)) :=
  completionZerothHomotopyKZeroEquiv_baseChange f (ZerothHomotopy.mk x)
