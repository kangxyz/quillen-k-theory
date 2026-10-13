/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricSpace.CoverRadius
public import Quillen.Topology.Realization.MetricPointStarRefinement

/-! The independent client supplies the frozen point-star lemma's radius
from an arbitrary original open cover. -/

@[expose] public section
noncomputable section

namespace Quillen.Consumer.MetricCoverRadius

variable {A κ : Type*} [MetricSpace A]

/-- An arbitrary original open metric cover has an actual open point-star-refining cover. -/
theorem exists_open_pointStar_refinement (V : κ → Set A) (hopen : ∀ k, IsOpen (V k))
    (hcover : ∀ x, ∃ k, x ∈ V k) :
    ∃ W : A → Set A, (∀ x, IsOpen (W x)) ∧ (∀ x, ∃ y, x ∈ W y) ∧
      NumerableConnectorCover.PointStarRefines W V := by
  obtain ⟨r, hpos, hLip, hsmall⟩ :=
    Quillen.MetricCoverRadius.exists_positive_lipschitz_radius V hopen hcover
  refine ⟨fun x ↦ Metric.ball x (r x / 8), fun _ ↦ Metric.isOpen_ball, ?_, ?_⟩
  · exact NumerableConnectorCover.radiusBalls_cover r hpos
  · exact NumerableConnectorCover.pointStarRefines_radius V r hpos hLip hsmall

end Quillen.Consumer.MetricCoverRadius
