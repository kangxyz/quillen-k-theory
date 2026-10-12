/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Plus.ProjectiveTelescopeKZero

/-! # The original telescope stage classes and unchanged Quillen K₀ -/

noncomputable section

open CategoryTheory
open Quillen Quillen.FiniteProjectiveModule Quillen.FiniteProjectiveModule.StableFreeRight

universe u

variable {R : Type u} [Ring R]

-- Every original diagonal finite-rank stage belongs to the algebraic zero component.
example (n : ℕ) :
    telescopeZerothHomotopyGrothendieckEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint
        (⟨n, AsSmall.up.obj (rankOnePower Rᵐᵒᵖ n)⟩ : ProjectiveTelescope R))) = 0 := by
  rw [telescopeZerothHomotopyGrothendieckEquiv_stage, sub_self]

-- The same actual stage is the identity class in the original homotopical K₀.
example (n : ℕ) :
    telescopeZerothHomotopyKZeroEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint
        (⟨n, AsSmall.up.obj (rankOnePower Rᵐᵒᵖ n)⟩ : ProjectiveTelescope R))) = 1 := by
  rw [telescopeZerothHomotopyKZeroEquiv_stage, div_self']

-- The original telescope has an actual finite-stage representative of every original K₀ class.
example (k : (exactStructure Rᵐᵒᵖ).K 0) :
    ∃ (n : ℕ) (P : IsoCategory Rᵐᵒᵖ),
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of = k := by
  obtain ⟨a, ha⟩ := (telescopeZerothHomotopyKZeroEquiv R).surjective k
  obtain ⟨⟨n, ⟨P⟩⟩, rfl⟩ := classifyingSpaceVertexComponent_surjective (ProjectiveTelescope R) a
  exact ⟨n, P, (telescopeZerothHomotopyKZeroEquiv_stage R n P).symm.trans ha⟩

-- Equality of original K₀ labels detects actual paths between arbitrary telescope points.
example (x y : ClassifyingSpace (ProjectiveTelescope R)) :
    telescopeZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk x) =
      telescopeZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk y) ↔ Joined x y := by
  rw [(telescopeZerothHomotopyKZeroEquiv R).injective.eq_iff]
  exact Quotient.eq
