/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.SimplexBoundaryFilling
public import Quillen.Topology.Realization.FiniteSimplexFamily
public import Quillen.Topology.Realization.SimplexFaceGluing

/-!
# One genuine relative step in finite simplex straightening

This owner constructs actual simplex homotopies from prescribed continuous
boundary tracks. Below the cutoff the endpoint is the constant simplex;
at and above the cutoff only genuine boundary HEP is used. The finite-family
version fixes the selected original simplices pointwise for the whole track.
Its indices are the actual continuous maps, so equal simplices share one
choice. Construction of the prescribed boundary tracks from lower face
homotopies is a separate obligation, not an assumption of a finished
straightening theorem.
-/

@[expose] public section
noncomputable section

open Convexity
open scoped Topology unitInterval

universe u

namespace Quillen

variable {Z : Type u} [TopologicalSpace Z]

/-- Two already coherent adjacent levels give the genuine continuous boundary
track of each next simplex. The double-face equality uses actual simplex
identity, so cancellation is not split into unrelated occurrence choices. -/
theorem exists_simplex_boundary_track_of_family (S : FiniteSimplexFamily Z)
    (hS : S.FaceClosed) (d : ℕ)
    (L : {s // s ∈ S d} → C(StdSimplex ℝ (Fin (d + 1)) × I, Z))
    (K : {s // s ∈ S (d + 1)} → C(StdSimplex ℝ (Fin (d + 2)) × I, Z))
    (hface : ∀ (s : {s // s ∈ S (d + 1)}) (i : Fin (d + 2))
      (x : StdSimplex ℝ (Fin (d + 1))) (t : I),
      K s (x.map i.succAbove, t) = L (hS.face s i) (x, t))
    (τ : {τ // τ ∈ S (d + 2)}) :
    ∃ H : C(simplexBoundary (d + 2) × I, Z),
      ∀ (i : Fin (d + 3)) (x : StdSimplex ℝ (Fin (d + 2))) (t : I),
        H (simplexBoundaryFace (d + 1) i x, t) = K (hS.face τ i) (x, t) := by
  apply exists_simplex_boundary_track_of_faces d (fun i ↦ K (hS.face τ i))
  intro i k q t
  rw [hface, hface, hS.face_face τ i k]

/-- Extend the prescribed side literally, choosing a constant endpoint exactly
in those dimensions in which the actual homotopy groups vanish. -/
theorem exists_simplex_straightening_step (n d : ℕ) (z : Z)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (f : C(StdSimplex ℝ (Fin (d + 1)), Z))
    (H : C(simplexBoundary d × I, Z))
    (hzero : ∀ b : simplexBoundary d, H (b, 0) = f b.val)
    (hone : d < n → ∀ b : simplexBoundary d, H (b, 1) = z) :
    ∃ g : C(StdSimplex ℝ (Fin (d + 1)), Z), ∃ K : f.Homotopy g,
      (∀ (b : simplexBoundary d) (t : I), K (t, b.val) = H (b, t)) ∧
      (d < n → g = ContinuousMap.const _ z) := by
  by_cases hd : d < n
  · obtain ⟨K, hK⟩ := exists_simplex_homotopy_of_boundary d (fun x ↦ hs x d hd)
      f (ContinuousMap.const _ z) H hzero (hone hd)
    exact ⟨ContinuousMap.const _ z, K, hK, fun _ ↦ rfl⟩
  · obtain ⟨g, K, hK⟩ := exists_simplex_homotopy_extension d f H hzero
    exact ⟨g, K, hK, fun h ↦ (hd h).elim⟩

/-- Make one relative straightening step simultaneously for a finite set of
actual singular simplices. Repeated occurrences of an equal map are the same
index. Already fixed simplices receive the literal stationary homotopy. -/
theorem exists_finite_simplex_straightening_step (n d : ℕ) (z : Z)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (S : Finset C(StdSimplex ℝ (Fin (d + 1)), Z))
    (F : Set C(StdSimplex ℝ (Fin (d + 1)), Z))
    (H : {s // s ∈ S} → C(simplexBoundary d × I, Z))
    (hzero : ∀ s (b : simplexBoundary d), H s (b, 0) = s.val b.val)
    (hone : d < n → ∀ s (b : simplexBoundary d), H s (b, 1) = z)
    (hfixed : ∀ s : {s // s ∈ S}, s.val ∈ F →
      ∀ (b : simplexBoundary d) (t : I), H s (b, t) = s.val b.val)
    (hcollapsed : ∀ s : {s // s ∈ S}, s.val ∈ F → d < n →
      s.val = ContinuousMap.const _ z) :
    ∃ g : {s // s ∈ S} → C(StdSimplex ℝ (Fin (d + 1)), Z),
      ∃ K : ∀ s : {s // s ∈ S}, s.val.Homotopy (g s), ∀ s : {s // s ∈ S},
        (∀ (b : simplexBoundary d) (t : I), K s (t, b.val) = H s (b, t)) ∧
        (d < n → g s = ContinuousMap.const _ z) ∧
        (s.val ∈ F → ∀ (t : I) (x : StdSimplex ℝ (Fin (d + 1))),
          K s (t, x) = s.val x) := by
  classical
  have hex (s : {s // s ∈ S}) :
      ∃ g : C(StdSimplex ℝ (Fin (d + 1)), Z), ∃ K : s.val.Homotopy g,
        (∀ (b : simplexBoundary d) (t : I), K (t, b.val) = H s (b, t)) ∧
        (d < n → g = ContinuousMap.const _ z) ∧
        (s.val ∈ F → ∀ (t : I) (x : StdSimplex ℝ (Fin (d + 1))),
          K (t, x) = s.val x) := by
    by_cases hmem : s.val ∈ F
    · exact ⟨s.val, ContinuousMap.Homotopy.refl s.val,
        fun b t ↦ (hfixed s hmem b t).symm, hcollapsed s hmem, fun _ _ _ ↦ rfl⟩
    · obtain ⟨g, K, hK, hg⟩ := exists_simplex_straightening_step n d z hs s.val
        (H s) (hzero s) (fun hd ↦ hone hd s)
      exact ⟨g, K, hK, hg, fun h ↦ (hmem h).elim⟩
  choose g K hside hconstant hstationary using hex
  exact ⟨g, K, fun s ↦ ⟨hside s, hconstant s, hstationary s⟩⟩

end Quillen
