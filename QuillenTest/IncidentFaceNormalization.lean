/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CubicalSubdivision.FaceNormalization

/-!
# Original incident-face normalization consumers

The local high-cell step consumes the proved support invariant on all lower incident faces
and retains the whole supplied boundary path. The low-cell consumer turns the same invariant
into avoidance when the required coordinate count exceeds the face dimension.
-/

@[expose] public section

open Quillen.CubicalSubdivision


noncomputable section

open scoped Topology unitInterval

universe u

namespace QuillenTest.IncidentFaceNormalization

open Quillen

open CubicalSubdivision

/-- In the low-dimensional branch the actual lower-face invariant excludes the bad subset
on the whole attaching boundary, ready for finite HELP into its complement. -/
theorem original_low_face_boundary_avoids {n m r : ℕ} (F : StageFace n m r)
    {Y : Type u} [TopologicalSpace Y] (v : C(skeletonBelow n m r, Y))
    (A : Set Y) (a b : unitInterval) (p : ℕ) (hr : r < p)
    (hv : ∀ (G : FaceIndex n m) (hG : faceDimension G < r),
      faceSet G ⊆ faceSet F.val → ∀ u : Active G → unitInterval,
        v ⟨face G u, Set.mem_iUnion.mpr ⟨⟨G, hG⟩, ⟨u, rfl⟩⟩⟩ ∈ A →
          u ∈ faceThinSupport G a b p)
    (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}) :
    v (stageBoundary F z) ∉ A := by
  intro hz
  exact not_mem_faceThinSupport_of_dimension_lt F.val a b p (F.property.trans_lt hr) z.val
    (boundary_faceThinSupport_of_lower F v A a b p hv z hz)

/-- A high face consumes all lower incident support estimates, then supplies the same endpoint
estimate on every containing face while keeping the original boundary path at every time. -/
theorem original_high_face_step {n m r : ℕ} (F : StageFace n m r)
    (a b : unitInterval) (hab : a < b) (p : ℕ) (hp : p ≤ r)
    {Y : Type u} [TopologicalSpace Y] (f : C((Active F.val → unitInterval), Y))
    (v : C(skeletonBelow n m r, Y)) (A : Set Y)
    (H : C(unitInterval ×
      {x : Active F.val → unitInterval // x ∈ _root_.Cube.boundary (Active F.val)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val) (hone : ∀ z, H (1, z) = v (stageBoundary F z))
    (hv : ∀ (G : FaceIndex n m) (hG : faceDimension G < r),
      faceSet G ⊆ faceSet F.val → ∀ u : Active G → unitInterval,
        v ⟨face G u, Set.mem_iUnion.mpr ⟨⟨G, hG⟩, ⟨u, rfl⟩⟩⟩ ∈ A →
          u ∈ faceThinSupport G a b p) :
    ∃ g : C((Active F.val → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ z, (⟨fun t ↦ K (t, z.val), by fun_prop⟩ : C(unitInterval, Y)) =
        ⟨fun t ↦ H (t, z), by fun_prop⟩) ∧
      ∀ (G : FaceIndex n m), faceSet F.val ⊆ faceSet G →
        ∀ (s : Active F.val → unitInterval) (t : Active G → unitInterval),
          face F.val s = face G t → g s ∈ A → t ∈ faceThinSupport G a b p := by
  have hb (z : {x : Active F.val → unitInterval // x ∈ _root_.Cube.boundary (Active F.val)})
      (hz : H (1, z) ∈ A) : z.val ∈ faceThinSupport F.val a b p := by
    apply boundary_faceThinSupport_of_lower F v A a b p hv z
    exact (hone z) ▸ hz
  obtain ⟨g, K, hK, hg⟩ := exists_face_boundary_track_incident_support F.val a b hab p
    (hp.trans_eq F.property.symm) f A H hzero hb
  exact ⟨g, K, fun z ↦ ContinuousMap.ext (fun t ↦ hK t z), hg⟩

/-- The same incident invariant feeds the low-cell HELP branch and produces an endpoint
avoiding the bad subset everywhere, with the prescribed whole boundary homotopy unchanged. -/
theorem original_low_face_step {n m r : ℕ} (F : StageFace n m r)
    (a b : unitInterval) (q : ℕ) (hr : r ≤ q)
    {Y : Type u} [TopologicalSpace Y] (f : C((Active F.val → unitInterval), Y))
    (v : C(skeletonBelow n m r, Y)) (A : Set Y)
    (hA : IsHomotopyConnectedMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Aᶜ), Y)) q)
    (H : C(unitInterval ×
      {x : Active F.val → unitInterval // x ∈ _root_.Cube.boundary (Active F.val)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val) (hone : ∀ z, H (1, z) = v (stageBoundary F z))
    (hv : ∀ (G : FaceIndex n m) (hG : faceDimension G < r),
      faceSet G ⊆ faceSet F.val → ∀ u : Active G → unitInterval,
        v ⟨face G u, Set.mem_iUnion.mpr ⟨⟨G, hG⟩, ⟨u, rfl⟩⟩⟩ ∈ A →
          u ∈ faceThinSupport G a b (q + 1)) :
    ∃ g : C((Active F.val → unitInterval), Y), (∀ s, g s ∉ A) ∧
      ∃ K : f.Homotopy g, ∀ t z, K (t, z.val) = H (t, z) := by
  have hb (z : {x : Active F.val → unitInterval // x ∈ _root_.Cube.boundary (Active F.val)}) :
      H (1, z) ∈ Aᶜ := by
    rw [hone z]
    exact original_low_face_boundary_avoids F v A a b (q + 1) (by omega) hv z
  obtain ⟨g, K, hK⟩ := exists_face_boundary_track_into F.val Aᶜ q hA
    (F.property.trans_le hr) f H hzero hb
  exact ⟨(⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Aᶜ), Y)).comp g,
    fun s ↦ (g s).property, K, hK⟩

/-- One proved local step works in every dimension and every mesh: the actual finite
connectivity is used below the cutoff and radial normalization above it. All incident support
estimates and the original full boundary track survive. -/
theorem original_all_dimensional_face_step {n m r : ℕ} (F : StageFace n m r)
    (a b : unitInterval) (hab : a < b) {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (q : ℕ)
    (hA : IsHomotopyConnectedMap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)) q)
    (f : C((Active F.val → unitInterval), Y)) (v : C(skeletonBelow n m r, Y))
    (H : C(unitInterval ×
      {x : Active F.val → unitInterval // x ∈ _root_.Cube.boundary (Active F.val)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val) (hone : ∀ z, H (1, z) = v (stageBoundary F z))
    (hv : ∀ (G : FaceIndex n m) (hG : faceDimension G < r),
      faceSet G ⊆ faceSet F.val → ∀ u : Active G → unitInterval,
        v ⟨face G u, Set.mem_iUnion.mpr ⟨⟨G, hG⟩, ⟨u, rfl⟩⟩⟩ ∉ A →
          u ∈ faceThinSupport G a b (q + 1)) :
    ∃ g : C((Active F.val → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ t z, K (t, z.val) = H (t, z)) ∧
      ∀ (G : FaceIndex n m), faceSet F.val ⊆ faceSet G →
        ∀ (s : Active F.val → unitInterval) (t : Active G → unitInterval),
          face F.val s = face G t → g s ∉ A → t ∈ faceThinSupport G a b (q + 1) := by
  have hb (z : {x : Active F.val → unitInterval // x ∈ _root_.Cube.boundary (Active F.val)})
      (hz : H (1, z) ∉ A) : z.val ∈ faceThinSupport F.val a b (q + 1) := by
    apply boundary_faceThinSupport_of_lower F v Aᶜ a b (q + 1) hv z
    exact (hone z) ▸ hz
  obtain ⟨g, K, hK, hg⟩ := exists_face_connected_normalization F.val a b hab A q hA f H hzero hb
  refine ⟨g, K, hK, ?_⟩
  intro G hFG s t h hnot
  exact faceThinSupport_of_subset F.val G hFG s t h a b (q + 1) (hg hnot)

/-- The coordinate restriction behind an incident-face support estimate is literal, including
all original grid parameters and the chosen common point. -/
theorem original_incident_coordinates {n m : ℕ} (F G : FaceIndex n m)
    (hFG : faceSet F ⊆ faceSet G) (s : Active F → unitInterval)
    (t : Active G → unitInterval) (h : face F s = face G t) (i : Active F) :
    t (activeEmbeddingOfSubset F G hFG i) = s i :=
  congrFun (parameters_restrict_of_subset F G hFG s t h) i

/-- A zero-dimensional original face has no positive support, regardless of its ambient mesh. -/
theorem original_zero_face_has_no_support {n m : ℕ} (F : FaceIndex n m)
    (hF : faceDimension F = 0) (a b : unitInterval) (p : ℕ)
    (t : Active F → unitInterval) : t ∉ faceThinSupport F a b (p + 1) :=
  not_mem_faceThinSupport_of_dimension_lt F a b (p + 1) (by omega) t

end QuillenTest.IncidentFaceNormalization
