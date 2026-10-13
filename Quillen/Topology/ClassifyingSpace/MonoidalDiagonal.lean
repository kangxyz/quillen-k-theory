/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.UnitalDiagonal
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Weak contractibility of a connected monoidal category with a normalized diagonal

This is the monoidal specialization of the unital-bifunctor criterion. The actual
left and right unitors agree at the unit by monoidal coherence. A natural map
from the identity to the tensor square, normalized to the inverse left unitor,
therefore trivializes all positive homotopy groups. Connectedness handles degree
zero; the conclusion is an actual weak equivalence to a point, not a contraction.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MonoidalCategory

namespace Quillen

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The left unitor for the original paired tensor functor. -/
def categoryUnitPairLeftTensorIso : categoryUnitPairLeft (𝟙_ C) ⋙ tensor C ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦ λ_ X) (by
    intro X Y f
    change (𝟙 (𝟙_ C) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f
    simp)

/-- The right unitor for the original paired tensor functor. -/
def categoryUnitPairRightTensorIso : categoryUnitPairRight (𝟙_ C) ⋙ tensor C ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦ ρ_ X) (by
    intro X Y f
    change (f ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
    simp)

/-- The actual classifying space of a connected monoidal category with a normalized
natural diagonal is weakly contractible. -/
theorem classifyingSpace_weaklyContractible_of_monoidalDiagonal [IsConnected C]
    (δ : 𝟭 C ⟶ Functor.diag C ⋙ tensor C)
    (hδ : δ.app (𝟙_ C) = (λ_ (𝟙_ C)).inv) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace C) (PUnit.unit : PUnit.{max u v + 1})) :=
  classifyingSpace_weaklyContractible_of_unitalDiagonal (𝟙_ C) (tensor C)
    categoryUnitPairLeftTensorIso categoryUnitPairRightTensorIso unitors_equal δ hδ

end Quillen
