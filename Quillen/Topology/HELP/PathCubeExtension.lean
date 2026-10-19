/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.Topology.Path.FamilyExtension
public import Quillen.Topology.HELP.CubicalHorn

/-!
# Fixed-endpoint path-family extension over finite cubes

An extension property for scalar maps on the boundary of the `(n + 1)`-cube implies an extension
property for families in `Path a b` on the boundary of the `n`-cube. The endpoints may differ.
The new path coordinate occupies coordinate zero of `stepHomeomorph`; all original cube
coordinates remain its tail. No time is identified with another parameter, and the complete
original boundary paths are recovered. The zero-dimensional case uses a one-dimensional
scalar extension and requires no separately supplied path between the endpoints.

This is a general geometric implication. It supplies no common-carrier lift for a native family
and proves no closure of Bass successor recipes.
-/

@[expose] public noncomputable section

open scoped Topology unitInterval

universe u v

namespace Quillen.CubicalTests

variable {X : Type v} [TopologicalSpace X] {a b : X}

private theorem isClosed_cubeBoundary (n : ℕ) :
    IsClosed {z : cube.{u} n | z.down ∈ Cube.boundary (Fin n)} := by
  change IsClosed {z : cube.{u} n | ∃ i : Fin n, z.down i = 0 ∨ z.down i = 1}
  simpa only [Set.ofPred_exists, Set.ofPred_or] using
    (isClosed_iUnion_of_finite fun i : Fin n ↦
      (isClosed_eq (by fun_prop : Continuous (fun z : cube.{u} n ↦ z.down i))
        continuous_const).union (isClosed_eq (by fun_prop) continuous_const))

/-- Scalar extension in one higher dimension extends a fixed-endpoint family of paths,
with equality of every whole boundary path in the original coordinates. -/
theorem exists_extend_path_boundary (n : ℕ)
    (extend : ∀ f : C(boundary.{u} (n + 1), X),
      ∃ F : C(cube.{u} (n + 1), X), F.comp (boundaryInclusion (n + 1)).hom = f)
    (p : C(boundary.{u} n, Path a b)) :
    ∃ P : C(cube.{u} n, Path a b), P.comp (boundaryInclusion n).hom = p := by
  have hext : ∀ f : C(ProductBoundary.{u} n, X),
      ∃ F : C(cube.{u} n × I, X), ∀ z : ProductBoundary.{u} n, F z.val = f z := by
    intro f
    obtain ⟨F, hF⟩ := extend (f.comp
      ⟨(productBoundaryHomeomorph n).symm, (productBoundaryHomeomorph n).symm.continuous⟩)
    refine ⟨F.comp ⟨stepHomeomorph n, (stepHomeomorph n).continuous⟩, ?_⟩
    intro z
    have hz := DFunLike.congr_fun hF (productBoundaryHomeomorph n z)
    change F (stepHomeomorph n z.val) =
      f ((productBoundaryHomeomorph n).symm (productBoundaryHomeomorph n z)) at hz
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      Homeomorph.symm_apply_apply] using hz
  obtain ⟨P, hP⟩ := Path.exists_family_extension (isClosed_cubeBoundary n) hext p
  refine ⟨P, ?_⟩
  exact ContinuousMap.ext hP

/-- Pointwise form exposing the independently variable original path time. -/
theorem exists_extend_path_boundary_apply (n : ℕ)
    (extend : ∀ f : C(boundary.{u} (n + 1), X),
      ∃ F : C(cube.{u} (n + 1), X), F.comp (boundaryInclusion (n + 1)).hom = f)
    (p : C(boundary.{u} n, Path a b)) :
    ∃ P : C(cube.{u} n, Path a b), ∀ (z : boundary.{u} n) (t : I), P z.val t = p z t := by
  obtain ⟨P, hP⟩ := exists_extend_path_boundary n extend p
  exact ⟨P, fun z t ↦ congrArg (fun q : Path a b ↦ q t) (DFunLike.congr_fun hP z)⟩

/-- The unlifted form matches existing finite-dimensional carrier extension producers exactly.
Only the harmless universe lift is removed; every original cube and path coordinate remains. -/
theorem exists_extend_path_unlifted_boundary (n : ℕ)
    (extend : ∀ f : C({z : Fin (n + 1) → I // z ∈ Cube.boundary (Fin (n + 1))}, X),
      ∃ F : C(Fin (n + 1) → I, X), F.restrict (Cube.boundary (Fin (n + 1))) = f)
    (p : C({z : Fin n → I // z ∈ Cube.boundary (Fin n)}, Path a b)) :
    ∃ P : C(Fin n → I, Path a b), P.restrict (Cube.boundary (Fin n)) = p := by
  have hext : ∀ f : C(boundary.{0} (n + 1), X),
      ∃ F : C(cube.{0} (n + 1), X), F.comp (boundaryInclusion (n + 1)).hom = f := by
    intro f
    obtain ⟨F, hF⟩ := extend (f.comp
      ⟨(boundaryULiftHomeomorph (n + 1)).symm,
        (boundaryULiftHomeomorph (n + 1)).symm.continuous⟩)
    refine ⟨F.comp ⟨Homeomorph.ulift.{0, 0}, Homeomorph.ulift.continuous⟩, ?_⟩
    ext z
    exact DFunLike.congr_fun hF ((boundaryULiftHomeomorph (n + 1)) z)
  obtain ⟨P, hP⟩ := exists_extend_path_boundary n hext
    (p.comp ⟨boundaryULiftHomeomorph n, (boundaryULiftHomeomorph n).continuous⟩)
  refine ⟨P.comp ⟨ULift.up, continuous_uliftUp⟩, ?_⟩
  apply ContinuousMap.ext
  intro z
  exact DFunLike.congr_fun hP ⟨⟨z.val⟩, z.property⟩

end Quillen.CubicalTests
