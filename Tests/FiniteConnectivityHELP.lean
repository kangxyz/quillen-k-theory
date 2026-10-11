/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HELP.Connectivity

/-!
# Consumers of finite connectivity and the original full boundary track

These tests use the actual map in every finite degree, compress an original cube into a
connected subspace while fixing its boundary, and retain a supplied nonconstant boundary
homotopy without replacing it by its endpoint data. Zero connectivity remains component
coverage, so empty-space and degree-zero cases do not silently gain higher connectivity.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.Tests.FiniteConnectivityHELP

open CubicalTests

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The top degree is genuinely surjective on the original homotopy map. -/
theorem original_endpoint_class_lift (f : C(X, Y)) (n : ℕ)
    (hf : IsHomotopyConnectedMap f n) (x : X) (a : HomotopyGroup.Pi n Y (f x)) :
    ∃ b : HomotopyGroup.Pi n X x, homotopyGroupMap f rfl b = a :=
  hf.homotopyGroupMap_surjective x n le_rfl a

/-- Reflection needs a strict degree inequality, and holds at every original source point. -/
theorem original_strict_range_class_reflection (f : C(X, Y)) (n k : ℕ)
    (hf : IsHomotopyConnectedMap f n) (hk : k < n) (x : X)
    (a b : HomotopyGroup.Pi k X x) (h : homotopyGroupMap f rfl a = homotopyGroupMap f rfl b) :
    a = b :=
  (hf.homotopyGroupMap_bijective x k hk).injective h

/-- The supplied entire boundary track survives in the extension at the limiting dimension. -/
theorem original_endpoint_boundary_track (f : C(X, Y)) (n : ℕ)
    (hf : IsHomotopyConnectedMap f n) (a : C(boundary.{u} n, X))
    (b : C(cube.{u} n, Y))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion n).hom)) :
    ∃ c : C(cube.{u} n, X), c.comp (boundaryInclusion n).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (z : boundary.{u} n),
          (⟨fun t ↦ K (t, z.val), by fun_prop⟩ : C(unitInterval, Y)) =
            ⟨fun t ↦ H (t, z), by fun_prop⟩ := by
  obtain ⟨c, hc, K, hK⟩ := hf.cube_fullHELP n le_rfl a b H
  refine ⟨c, hc, K, fun z ↦ ?_⟩
  exact ContinuousMap.ext (fun t ↦ hK t z)

/-- A low-dimensional original cube whose boundary lies in the subspace can be compressed
into that subspace. The actual comparison fixes every boundary point at every time. -/
theorem original_subspace_cube_compression (A : Set Y) (n m : ℕ)
    (hA : IsHomotopyConnectedMap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)) n)
    (hm : m ≤ n) (b : C(cube.{u} m, Y)) (hb : ∀ z : boundary.{u} m, b z.val ∈ A) :
    ∃ c : C(cube.{u} m, Y), (∀ z, c z ∈ A) ∧
      Nonempty (b.HomotopyRel c (Set.range (boundaryInclusion m))) := by
  let i : C(A, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let a : C(boundary.{u} m, A) :=
    ⟨fun z ↦ ⟨b z.val, hb z⟩, (b.continuous.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨c, _, ⟨K⟩⟩ := hA.cube_strictHELP m hm a b rfl
  exact ⟨i.comp c, fun z ↦ (c z).property, ⟨K.symm⟩⟩

/-- In dimension zero the conclusion is an actual original fiber point and its path. -/
theorem original_zero_connectivity_fiber_point (f : C(X, Y))
    (hf : IsHomotopyConnectedMap f 0) (y : Y) :
    ∃ x : X, Nonempty (Path (f x) y) := by
  obtain ⟨x, hx⟩ := hf.component_surjective y
  exact ⟨x, hx⟩

/-- Contracting the actual cube base transfers the finite bound to any pullback point,
without selecting a constant-path component. -/
theorem original_cube_pullback_all_points (f : C(X, Y)) (n m : ℕ)
    (hf : IsHomotopyConnectedMap f n) (b : C(cube.{u} m, Y))
    (z : HomotopyPullback f b) (k : ℕ) (hk : k < n) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyPullback f b) z) :=
  HomotopyPullback.subsingleton_homotopyGroup_of_contraction
    f b hf (zero m) (contraction m) z k hk

end Quillen.Tests.FiniteConnectivityHELP
