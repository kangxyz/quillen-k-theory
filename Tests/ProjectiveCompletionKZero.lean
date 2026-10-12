/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Plus.ProjectiveCompletionKZero

/-! # Original projective completion components and genuine K₀ -/

noncomputable section

open CategoryTheory
open Quillen Quillen.FiniteProjectiveModule

universe u

variable {R S : Type u} [Ring R] [Ring S]

-- Equality in the original homotopical K₀ detects actual finite categorical zigzags.
example (X Y : GroupCompletionCategory R) :
    completionKZeroClass R X = completionKZeroClass R Y ↔ Zigzag X Y := by
  change completionComponentKZeroEquiv R (CategoryTheory.ConnectedComponents.mk X) =
      completionComponentKZeroEquiv R (CategoryTheory.ConnectedComponents.mk Y) ↔ _
  rw [(completionComponentKZeroEquiv R).injective.eq_iff]
  exact Quotient.eq

-- The unchanged K₀ map detects precisely the components collapsed by actual change of rings.
example (f : R →+* S) (a b : CompletionComponents Rᵐᵒᵖ) :
    (rightBaseChangeExact f).KMap 0 (completionComponentKZeroEquiv Rᵐᵒᵖ a) =
      (rightBaseChangeExact f).KMap 0 (completionComponentKZeroEquiv Rᵐᵒᵖ b) ↔
    completionComponentsBaseChange f a =
      completionComponentsBaseChange f b := by
  rw [completionComponentKZeroEquiv_baseChange, completionComponentKZeroEquiv_baseChange]
  exact (completionComponentKZeroEquiv Sᵐᵒᵖ).injective.eq_iff

-- The inverse of the original grade sends every projective generator to its actual unit entrance.
example (P : Quillen.FiniteProjectiveModule.Category.{u, u} R) :
    (completionComponentGrothendieckEquiv R).symm
      ((exactStructure R).grothendieckClass P) = projectiveCompletionClass R P :=
  grothendieckToCompletionComponents_class R P
