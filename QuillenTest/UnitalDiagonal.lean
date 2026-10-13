/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.ClassifyingSpace.MonoidalDiagonal

/-! Consumer checks: the criterion reaches every topological point and includes degree zero. -/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory

namespace QuillenTest

open Quillen

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsConnected C]
  (δ : 𝟭 C ⟶ Functor.diag C ⋙ tensor C)
  (hδ : δ.app (𝟙_ C) = (λ_ (𝟙_ C)).inv)

include δ hδ in
example (x : ClassifyingSpace C) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n (ClassifyingSpace C) x) := by
  have h := (classifyingSpace_weaklyContractible_of_monoidalDiagonal δ hδ).homotopy_bijective x n
  let := subsingleton_pi_of_contractible n PUnit.{max u v + 1} PUnit.unit
  exact h.injective.subsingleton

include δ hδ in
example : ∀ y : PUnit.{max u v + 1}, ∃ x : ClassifyingSpace C,
    Joined ((ContinuousMap.const (ClassifyingSpace C) PUnit.unit) x) y :=
  (classifyingSpace_weaklyContractible_of_monoidalDiagonal δ hδ).component_surjective

end QuillenTest
