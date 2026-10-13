/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Cube.ThinSupport

/-!
# Coordinate-embedding compatibility of the actual thin supports

A lower face retains a subset of the original parameter coordinates. Its band coordinates
embed into the ambient face's band coordinates, so the same support bound remains true.
This is the finite-coordinate input for compatibility of normalization across incident faces.
-/

@[expose] public section

noncomputable section

open scoped Topology unitInterval

namespace Quillen.Cube

/-- Actual band coordinates on a subfamily inject into those on the whole family. -/
theorem bandCoordinates_map_subset {d n : ℕ} (a b : unitInterval)
    (e : Fin d ↪ Fin n) (x : Fin n → unitInterval) :
    (bandCoordinates a b (x ∘ e)).map e ⊆ bandCoordinates a b x := by
  classical
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  simpa only [bandCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply] using hj

/-- A lower face's support bound holds for the unchanged larger coordinate family. -/
theorem thinSupport_of_coordinateEmbedding {d n : ℕ} (a b : unitInterval)
    (e : Fin d ↪ Fin n) (x : Fin n → unitInterval) (p : ℕ)
    (hx : x ∘ e ∈ thinSupport a b p) : x ∈ thinSupport a b p := by
  have h := Finset.card_le_card (bandCoordinates_map_subset a b e x)
  rw [Finset.card_map] at h
  exact hx.trans h

/-- Reindexing the same original coordinate family preserves the exact band count. -/
theorem bandCoordinates_reindex_card {d n : ℕ} (a b : unitInterval)
    (e : Fin d ≃ Fin n) (x : Fin n → unitInterval) :
    (bandCoordinates a b (x ∘ e)).card = (bandCoordinates a b x).card := by
  classical
  have h : (bandCoordinates a b (x ∘ e)).map e.toEmbedding = bandCoordinates a b x := by
    apply Finset.Subset.antisymm (bandCoordinates_map_subset a b e.toEmbedding x)
    intro i hi
    apply Finset.mem_map.mpr
    refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
    simpa only [bandCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using hi
  rw [← h, Finset.card_map]

end Quillen.Cube
