/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.ProductFiberHELP
public import Quillen.Topology.HELP.TwoOfThree

/-! # Compact HELP for the original constant-path split fiber inclusion

The actual first projection is a compact HELP map and the original inclusion
is its strict section, including its unchanged constant path coordinate.
Two-of-three gives HELP for this inclusion and any actual split transition.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
namespace Quillen.SplitRealizationFiber
variable {A B E : SSet.{u}} (χ : E ⟶ A ⊗ B)
  (s : A ⟶ E) (y : B _⦋0⦌) (hs : s ≫ χ = ProductRealization.vertexSection A B y)

/-- The original constant-path inclusion is a literal section of the actual
first projection, as an equality of continuous maps. -/
theorem firstProjection_inclusion :
    (firstProjection χ (realizationPoint y)).comp (inclusion χ s y hs) =
      ContinuousMap.id |A| := by
  change ((ProductRealization.fiberProjection A B (realizationPoint y)).comp
    (comparison χ (realizationPoint y))).comp (inclusion χ s y hs) = _
  rw [ContinuousMap.comp_assoc, comparison_inclusion χ s y hs]
  exact ProductRealization.fiberProjection_inclusion A B y

/-- Compact HELP for the prescribed original split inclusion, retaining its
constant path literally and without a fiber-equivalence premise. -/
theorem inclusion_compactHELP (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom) :
    CompactHomotopyExtensionLiftingProperty (inclusion χ s y hs) :=
  compactHELP_section (firstProjection_compactHELP χ e he (realizationPoint y))
    (firstProjection_inclusion χ s y hs)

/-- An actual transition preserving the split inclusion has compact HELP.
The transition's homotopy-fiber path coordinate is not modified. -/
theorem transition_compactHELP
    {B' E' : SSet.{u}} (χ' : E' ⟶ A ⊗ B') (s' : A ⟶ E') (y' : B' _⦋0⦌)
    (hs' : s' ≫ χ' = ProductRealization.vertexSection A B' y')
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom)
    (e' : ContinuousMap.HomotopyEquiv |E'| |A ⊗ B'|)
    (he' : e'.toFun = (SSet.toTop.map χ').hom)
    (t : C(HomotopyFiber (projection χ) (realizationPoint y),
      HomotopyFiber (projection χ') (realizationPoint y')))
    (ht : t.comp (inclusion χ s y hs) = inclusion χ' s' y' hs') :
    CompactHomotopyExtensionLiftingProperty t :=
  compactHELP_transition (inclusion_compactHELP χ s y hs e he)
    (inclusion_compactHELP χ' s' y' hs' e' he') ht

end Quillen.SplitRealizationFiber
