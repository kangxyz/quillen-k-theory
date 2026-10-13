/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricSpace.CoverRadius

/-! Named radius regressions for the exact cover API, whole-space members, and empty indices. -/

@[expose] public section
noncomputable section

namespace QuillenTest.MetricCoverRadius

open Quillen

open Quillen.MetricCoverRadius

variable {A κ : Type*} [PseudoMetricSpace A]

/-- The actual constructed radius is positive, bounded, Lipschitz, and subordinate at half size. -/
theorem constructed_radius_contract (V : κ → Set A) (hopen : ∀ k, IsOpen (V k))
    (hcover : ∀ x, ∃ k, x ∈ V k) :
    (∀ x, 0 < radius V x ∧ radius V x ≤ 1) ∧ LipschitzWith 1 (radius V) ∧
      ∀ x, ∃ k, Metric.ball x (radius V x / 2) ⊆ V k :=
  ⟨fun x ↦ ⟨radius_pos V hopen hcover x, radius_le_one V hcover x⟩,
    lipschitz_radius V hcover, half_radius_subordinate V hopen hcover⟩

/-- A whole-space cover member is allowed without any nonempty-complement premise. -/
theorem whole_space_cover :
    ∃ r : A → ℝ, (∀ x, 0 < r x) ∧ LipschitzWith 1 r ∧
      ∀ x, ∃ k : Unit, Metric.ball x (r x / 2) ⊆ (fun _ : Unit ↦ (Set.univ : Set A)) k :=
  exists_positive_lipschitz_radius (fun _ : Unit ↦ (Set.univ : Set A))
    (fun _ ↦ isOpen_univ) (fun x ↦ ⟨(), Set.mem_univ x⟩)

/-- Both the space and cover index may be empty; no cover member is selected globally. -/
theorem empty_space_empty_index :
    ∃ r : Empty → ℝ, (∀ x, 0 < r x) ∧ LipschitzWith 1 r ∧
      ∀ x, ∃ k : Empty, Metric.ball x (r x / 2) ⊆ (Empty.elim k : Set Empty) :=
  exists_positive_lipschitz_radius (fun k : Empty ↦ (Empty.elim k : Set Empty))
    (fun k ↦ Empty.elim k) (fun x ↦ Empty.elim x)

omit [PseudoMetricSpace A] in
/-- An empty index cannot cover an actual supplied point of a nonempty space. -/
theorem empty_index_cannot_cover (x : A) (V : Empty → Set A) :
    ¬ (∀ y, ∃ k, y ∈ V k) := by
  intro h
  obtain ⟨k, _⟩ := h x
  exact Empty.elim k

/-- The metric ball argument treats every nonpositive radius as genuinely empty. -/
theorem nonpositive_ball_empty (x : A) (t : ℝ) (ht : t ≤ 0) : Metric.ball x t = ∅ :=
  Metric.ball_eq_empty.mpr ht

end QuillenTest.MetricCoverRadius
