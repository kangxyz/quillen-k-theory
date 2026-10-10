/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.SplitFiberCartesian
public import Quillen.Topology.Realization.SplitFiberCompactHELP

/-! # Full compact HELP for the original split-row fiber transition

The target first projection cancels the original transition and source split
inclusion literally. The proved compact HELP properties of those two maps and
full-boundary two-of-three give HELP of the unchanged transition. No fiber
conclusion or continuous choice of inverses is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
namespace Quillen.SplitRealizationFiber
variable {A B E B' E' : SSet.{u}}
  (χ : E ⟶ A ⊗ B) (χ' : E' ⟶ A ⊗ B')
  (s : A ⟶ E) (s' : A ⟶ E') (y : B _⦋0⦌) (y' : B' _⦋0⦌)
  (hs : s ≫ χ = ProductRealization.vertexSection A B y)
  (hs' : s' ≫ χ' = ProductRealization.vertexSection A B' y')
  (a : E ⟶ E') (b : B ⟶ B')
  (sq : a ≫ χ' ≫ snd A B' = χ ≫ snd A B ≫ b)
  (ha : s ≫ a = s')
include hs hs' ha

/-- Full compact HELP of the original transition, derived from genuine
row product equivalences and the natural split section. The target fiber
is over the literal base image; no identification of chosen points is assumed. -/
theorem transition_compactHELP_of_natural_split
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom)
    (e' : ContinuousMap.HomotopyEquiv |E'| |A ⊗ B'|)
    (he' : e'.toFun = (SSet.toTop.map χ').hom) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyPullback.transitionFiber (projection χ) (projection χ')
        (SSet.toTop.map a).hom (SSet.toTop.map b).hom
        (transitionSquare χ χ' a b sq) (realizationPoint y)) := by
  let t := HomotopyPullback.transitionFiber (projection χ) (projection χ')
    (SSet.toTop.map a).hom (SSet.toTop.map b).hom
    (transitionSquare χ χ' a b sq) (realizationPoint y)
  let i := inclusion χ s y hs
  let p := firstProjection χ' (SSet.toTop.map b (realizationPoint y))
  have hpti : CompactHomotopyExtensionLiftingProperty (p.comp (t.comp i)) := by
    rw [firstProjection_transition_inclusion χ χ' s s' y y' hs hs' a b sq ha]
    exact compactHELP_of_homotopyEquiv (ContinuousMap.HomotopyEquiv.refl |A|)
  exact (hpti.cancel_second (firstProjection_compactHELP χ' e' he' _)).cancel_first
    (inclusion_compactHELP χ s y hs e he)

end Quillen.SplitRealizationFiber
