/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.CubicalSubdivision.ConnectivityLifting
public import Quillen.Topology.Cube.BoundaryHomotopyNormalization

/-!
# Original grid-stage and overlap consumers

The grid dimension, mesh and attaching dimension remain explicit. The original source map
and supplied boundary paths are retained on overlaps, including arbitrary times. Compression
into a connected subspace uses the proved finite-range HELP rather than a lifting premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u

namespace Quillen.Tests.GridConnectivityHELP

open CubicalSubdivision

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Two originally prescribed face paths agree as whole continuous paths whenever their
original face points coincide. The assembled homotopy retains both original restrictions. -/
theorem original_intersection_paths (n m r : ℕ)
    (f : C(X, Y)) (a : C(skeletonBelow n m r, X)) (b : C(skeleton n m r, Y))
    (H : (f.comp a).Homotopy (b.comp (stageInclusion n m r)))
    (c : ∀ F : StageFace n m r, C((Active F.val → unitInterval), X))
    (hc : ∀ F (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}),
      c F z.val = a (stageBoundary F z))
    (K : ∀ F : StageFace n m r, (f.comp (c F)).Homotopy (b.comp (stageFaceMap F)))
    (hK : ∀ F (t : unitInterval)
      (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}),
      K F (t, z.val) = H (t, stageBoundary F z))
    (F G : StageFace n m r) (x : Active F.val → unitInterval)
    (y : Active G.val → unitInterval) (hxy : face F.val x = face G.val y) :
    (⟨fun t ↦ K F (t, x), by fun_prop⟩ : C(unitInterval, Y)) =
      ⟨fun t ↦ K G (t, y), by fun_prop⟩ := by
  obtain ⟨_, _, _, L, _, hL⟩ := exists_stage_homotopy_paste n m r f a b H c hc K hK
  apply ContinuousMap.ext
  intro t
  exact (hL F t x).symm.trans
    ((congrArg (fun z ↦ L (t, z)) (Subtype.ext hxy)).trans (hL G t y))

/-- At the limiting attaching dimension the given homotopy remains the identical whole path
on every point of the preceding skeleton. -/
theorem original_limiting_stage_track (f : C(X, Y)) (q n m : ℕ)
    (hf : IsHomotopyConnectedMap f q) (a : C(skeletonBelow n m q, X))
    (b : C(skeleton n m q, Y))
    (H : (f.comp a).Homotopy (b.comp (stageInclusion n m q))) :
    ∃ g : C(skeleton n m q, X), g.comp (stageInclusion n m q) = a ∧
      ∃ L : (f.comp g).Homotopy b,
        ∀ x, (⟨fun t ↦ L (t, stageInclusion n m q x), by fun_prop⟩ : C(unitInterval, Y)) =
          ⟨fun t ↦ H (t, x), by fun_prop⟩ := by
  obtain ⟨g, hg, L, hL⟩ := stage_fullHELP hf n m q le_rfl a b H
  exact ⟨g, hg, L, fun x ↦ ContinuousMap.ext (fun t ↦ hL t x)⟩

/-- The genuine finite fiber hypothesis compresses the actual next skeleton into the
subspace, fixing the old skeleton throughout. This includes the zero-dimensional stage. -/
theorem original_subspace_stage_compression (A : Set Y) (q n m r : ℕ)
    (hA : IsHomotopyConnectedMap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)) q)
    (hr : r ≤ q) (b : C(skeleton n m r, Y))
    (hb : ∀ x, b (stageInclusion n m r x) ∈ A) :
    ∃ g : C(skeleton n m r, Y), (∀ x, g x ∈ A) ∧
      Nonempty (b.HomotopyRel g (Set.range (stageInclusion n m r))) := by
  let i : C(A, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let a : C(skeletonBelow n m r, A) :=
    ⟨fun x ↦ ⟨b (stageInclusion n m r x), hb x⟩, by fun_prop⟩
  obtain ⟨g, _, ⟨L⟩⟩ := stage_strictHELP hA n m r hr a b rfl
  exact ⟨i.comp g, fun x ↦ (g x).property, ⟨L.symm⟩⟩

/-- At zero connectivity, all original vertices lift up to actual paths without requiring
connected fibers or any positive-degree hypothesis. -/
theorem original_vertex_stage_lift (f : C(X, Y)) (n m : ℕ)
    (hf : IsHomotopyConnectedMap f 0) (b : C(skeleton n m 0, Y)) :
    ∃ g : C(skeleton n m 0, X), Nonempty ((f.comp g).Homotopy b) := by
  let : IsEmpty (skeletonBelow n m 0) := ⟨fun x ↦ by
    have hx := x.property
    simp only [skeletonBelow_zero, Set.mem_empty_iff_false] at hx⟩
  let a : C(skeletonBelow n m 0, X) := ⟨isEmptyElim, continuous_of_discreteTopology⟩
  have w : f.comp a = b.comp (stageInclusion n m 0) :=
    ContinuousMap.ext (fun x ↦ isEmptyElim x)
  obtain ⟨g, _, ⟨L⟩⟩ := stage_strictHELP hf n m 0 le_rfl a b w
  exact ⟨g, ⟨L.toHomotopy⟩⟩

/-- The same-time radial construction retains arbitrary specified boundary path values, while
the two normalized endpoint inverse images cannot intersect in disjoint coordinate bands. -/
theorem original_normalized_endpoints_disjoint {d : ℕ}
    (a b c e : unitInterval) (hab : a < b) (hce : c < e) (hbc : b ≤ c)
    (p q : ℕ) (hp : p ≤ d) (hq : q ≤ d) (hd : d < p + q)
    (f g : C((Fin d → unitInterval), Y)) (A B : Set Y)
    (H J : C(unitInterval ×
      {x : Fin d → unitInterval // x ∈ _root_.Cube.boundary (Fin d)}, Y))
    (hHzero : ∀ z, H (0, z) = f z.val) (hJzero : ∀ z, J (0, z) = g z.val)
    (hH : ∀ z, H (1, z) ∈ A → z.val ∈ Cube.thinSupport a b p)
    (hJ : ∀ z, J (1, z) ∈ B → z.val ∈ Cube.thinSupport c e q) :
    ∃ f' g' : C((Fin d → unitInterval), Y),
      ∃ K : f.Homotopy f', ∃ L : g.Homotopy g',
        (∀ t z, K (t, z.val) = H (t, z)) ∧
        (∀ t z, L (t, z.val) = J (t, z)) ∧
        ∀ x, f' x ∈ A → g' x ∉ B := by
  obtain ⟨f', K, hK, hA⟩ := Cube.exists_boundary_track_thinSupport a b hab p hp f A H hHzero hH
  obtain ⟨g', L, hL, hB⟩ := Cube.exists_boundary_track_thinSupport c e hce q hq g B J hJzero hJ
  refine ⟨f', g', K, L, hK, hL, ?_⟩
  intro x hx hy
  exact Set.disjoint_left.mp (Cube.thinSupport_disjoint a b c e hbc p q hd) (hA hx) (hB hy)

/-- With no cube coordinates, simultaneous normalization still evaluates the original
extension at the identical time, rather than introducing a boundary or a new path. -/
theorem original_zero_cube_simultaneous_time (a b : unitInterval) (hab : a < b)
    (J : C(unitInterval × (Fin 0 → unitInterval), Y)) (t : unitInterval)
    (x : Fin 0 → unitInterval) :
    Cube.simultaneousBandNormalization a b hab J (t, x) = J (t, x) := by
  exact congrArg (fun x ↦ J (t, x)) (Subsingleton.elim _ _)

end Quillen.Tests.GridConnectivityHELP
