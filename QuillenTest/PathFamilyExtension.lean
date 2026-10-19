/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.HELP.PathCubeExtension

/-! # Fixed endpoints, the empty boundary, and independent iterated path times -/

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public noncomputable section

open scoped Topology unitInterval

universe u v

namespace QuillenTest.PathFamilyExtension

open Quillen.CubicalTests

variable {X : Type v} [TopologicalSpace X] {a b : X}

/-- Dimension zero constructs a path between the two supplied tips without assuming one. -/
theorem zero_dimension (extend : ∀ f : C(boundary.{u} 1, X),
    ∃ F : C(cube.{u} 1, X), F.comp (boundaryInclusion 1).hom = f) :
    Nonempty (Path a b) := by
  let : IsEmpty (boundary.{u} 0) := ⟨fun z ↦ by
    obtain ⟨i, _⟩ := z.property
    exact Fin.elim0 i⟩
  let p : C(boundary.{u} 0, Path a b) :=
    ⟨isEmptyElim, continuous_iff_continuousAt.mpr fun z ↦ isEmptyElim z⟩
  obtain ⟨P, _⟩ := exists_extend_path_boundary 0 extend p
  exact ⟨P (zero 0)⟩

/-- Repeating the implication spends two scalar dimensions and retains both independent times. -/
theorem two_independent_times (n : ℕ) (P Q : Path a b)
    (extend : ∀ f : C(boundary.{u} (n + 1 + 1), X),
      ∃ F : C(cube.{u} (n + 1 + 1), X), F.comp (boundaryInclusion (n + 1 + 1)).hom = f)
    (p : C(boundary.{u} n, Path P Q)) :
    ∃ E : C(cube.{u} n, Path P Q),
      ∀ (z : boundary.{u} n) (r s : I), E z.val r s = p z r s := by
  obtain ⟨E, hE⟩ := exists_extend_path_boundary n
    (exists_extend_path_boundary (n + 1) extend) p
  exact ⟨E, fun z r s ↦ congrArg (fun q : Path P Q ↦ q r s) (DFunLike.congr_fun hE z)⟩

/-- The generic closed-subset construction returns the supplied scalar map at every point. -/
theorem original_scalar_values {B : Type u} [TopologicalSpace B] {S : Set B}
    (hS : IsClosed S) (p : C(S, Path a b)) (F : C(B × I, X))
    (hF : ∀ z : Path.FamilyBoundary S, F z.val = Path.familyBoundaryMap hS p z)
    (z : B) (t : I) : Path.familyExtension hS p F hF z t = F (z, t) := rfl

/-- Distinct concrete tips are retained on the two caps, with no endpoint identification. -/
theorem distinct_interval_tips {B : Type u} [TopologicalSpace B] {S : Set B}
    (hS : IsClosed S) (p : C(S, Path (0 : I) 1)) (z : B) :
    Path.familyBoundaryMap hS p ⟨(z, 0), Or.inr (Or.inl rfl)⟩ ≠
      Path.familyBoundaryMap hS p ⟨(z, 1), Or.inr (Or.inr rfl)⟩ := by
  simp

end QuillenTest.PathFamilyExtension
