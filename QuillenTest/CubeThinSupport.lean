/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Cube.ThinSupport

/-!
# Original-map consumers of boundary-fixed thin-support normalization

Two actual normalized cube maps cannot simultaneously hit their bad subsets when their disjoint
coordinate bands require more coordinates than the source dimension. Whole boundary tracks,
full-dimensional support, and the zero-dimensional cube are tested on the original explicit maps.
-/

@[expose] public section

noncomputable section

open scoped Topology unitInterval
open Quillen.Cube

universe u v

namespace QuillenTest.CubeThinSupport

open Quillen

/-- The elementary two-color coordinate-counting step applies to the two original normalized
maps, with no topological assumption on either bad subset or either target beyond topology. -/
theorem original_normalized_maps_cannot_both_hit
    {d p q : ℕ} (hp : p ≤ d) (hq : q ≤ d) (hd : d < p + q)
    (a b c e : unitInterval) (hab : a < b) (hce : c < e) (hbc : b ≤ c)
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C((Fin d → unitInterval), Y)) (g : C((Fin d → unitInterval), Z))
    (A : Set Y) (B : Set Z)
    (hf : ∀ x ∈ _root_.Cube.boundary (Fin d), f x ∈ A → x ∈ thinSupport a b p)
    (hg : ∀ x ∈ _root_.Cube.boundary (Fin d), g x ∈ B → x ∈ thinSupport c e q)
    (x : Fin d → unitInterval) (hx : f (bandExpansion a b hab x) ∈ A) :
    g (bandExpansion c e hce x) ∉ B := by
  intro hy
  exact Set.disjoint_left.mp (thinSupport_disjoint a b c e hbc p q hd)
    (preimage_subset_thinSupport a b hab p hp f A hf hx)
    (preimage_subset_thinSupport c e hce q hq g B hg hy)

/-- Every original boundary point remains fixed for the entire actual target homotopy. -/
theorem original_normalization_boundary_track {d : ℕ} (a b : unitInterval) (hab : a < b)
    {Y : Type u} [TopologicalSpace Y] (f : C((Fin d → unitInterval), Y))
    (x : Fin d → unitInterval) (hx : x ∈ _root_.Cube.boundary (Fin d)) (r : unitInterval) :
    ((bandExpansionHomotopy a b hab).compContinuousMap f) (r, x) = f x :=
  ((bandExpansionHomotopy a b hab).compContinuousMap f).prop r x hx

/-- When the original boundary avoids the bad subset, every bad value of the actual normalized
map has all d coordinates in the band; this includes the endpoint case p=d. -/
theorem original_full_dimension_support {d : ℕ} (a b : unitInterval) (hab : a < b)
    {Y : Type u} [TopologicalSpace Y] (f : C((Fin d → unitInterval), Y)) (A : Set Y)
    (hf : ∀ x ∈ _root_.Cube.boundary (Fin d), f x ∉ A)
    (x : Fin d → unitInterval) (hx : f (bandExpansion a b hab x) ∈ A) :
    ∀ i, a < x i ∧ x i < b := by
  by_contra h
  exact hf (bandExpansion a b hab x) (bandExpansion_mem_boundary_of_not_all a b hab x h) hx

/-- The original zero-dimensional expansion is literally the identity, without any chosen point. -/
theorem original_zero_cube_fixed (a b : unitInterval) (hab : a < b)
    (x : Fin 0 → unitInterval) : bandExpansion a b hab x = x := by
  funext i
  exact Fin.elim0 i

/-- Requiring zero band coordinates imposes no condition even on a zero-dimensional cube. -/
theorem original_zero_support {d : ℕ} (a b : unitInterval) (x : Fin d → unitInterval) :
    x ∈ thinSupport a b 0 := by
  rw [thinSupport_zero]
  trivial

/-- The original radial center is fixed for every positive cap, even away from midpoint 1/2. -/
theorem original_radial_center_fixed {d : ℕ} (c ε : unitInterval)
    (hc₀ : 0 < (c : ℝ)) (hc₁ : (c : ℝ) < 1) (hε : 0 < (ε : ℝ)) :
    radialExpansion (d := d) c ε hc₀ hc₁ hε (fun _ ↦ c) = fun _ ↦ c := by
  funext i
  apply Subtype.ext
  change (c : ℝ) + ((c : ℝ) - c) / radialScale c ε (fun _ : Fin d ↦ c) = c
  simp

end QuillenTest.CubeThinSupport
