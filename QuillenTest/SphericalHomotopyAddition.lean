/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.SphericalHomotopyAddition

/-! Named regressions for the complete four-face tetrahedral relation,
the next-dimensional sign, and the actual quotient-face representatives. -/

@[expose] public section
noncomputable section
open Convexity
open scoped Topology unitInterval
universe u
namespace QuillenTest.SphericalHomotopyAddition

open Quillen
variable {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- All four surviving tetrahedral faces retain their literal increasing parametrizations. -/
theorem tetrahedral_surviving_faces (τ : C(StdSimplex ℝ (Fin 4), Z))
    (hτ : ∀ x ∈ simplexSkeleton 2 3, τ x = z) :
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
        0 0 (Or.inl rfl) = (sphericalFace τ hτ 0).toGenLoopStick ∧
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
        1 0 (Or.inl rfl) = (sphericalFace τ hτ 1).toGenLoopStick ∧
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
        2 0 (Or.inl rfl) = (sphericalFace τ hτ 2).toGenLoopStick ∧
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
        2 1 (Or.inr rfl) = (sphericalFace τ hτ 3).toGenLoopStick :=
  ⟨stickSimplexCube_lowerFace τ hτ 0, stickSimplexCube_lowerFace τ hτ 1,
    stickSimplexCube_lowerFace τ hτ 2, stickSimplexCube_upperFace_last τ hτ⟩

/-- The two extra cube faces are actually constant before taking homotopy classes. -/
theorem tetrahedral_collapsed_faces (τ : C(StdSimplex ℝ (Fin 4), Z))
    (hτ : ∀ x ∈ simplexSkeleton 2 3, τ x = z) :
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
        0 1 (Or.inr rfl) = GenLoop.const ∧
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
        1 1 (Or.inr rfl) = GenLoop.const :=
  ⟨stickSimplexCube_upperFace_const τ hτ 0 (by decide),
    stickSimplexCube_upperFace_const τ hτ 1 (by decide)⟩

/-- The n=2 test retains the required fourth face with coefficient minus one. -/
theorem tetrahedral_four_face_relation (τ : C(StdSimplex ℝ (Fin 4), Z))
    (hτ : ∀ x ∈ simplexSkeleton 2 3, τ x = z) :
    Additive.ofMul (sphericalFace τ hτ 0).homotopyClassStick -
      Additive.ofMul (sphericalFace τ hτ 1).homotopyClassStick +
      Additive.ofMul (sphericalFace τ hτ 2).homotopyClassStick -
      Additive.ofMul (sphericalFace τ hτ 3).homotopyClassStick =
        (0 : Additive (HomotopyGroup.Pi 2 Z z)) :=
  spherical_tetrahedral_homotopy_addition τ hτ

/-- In the next dimension the final fifth face has coefficient plus one. -/
theorem degree_three_five_face_relation (τ : C(StdSimplex ℝ (Fin 5), Z))
    (hτ : ∀ x ∈ simplexSkeleton 3 4, τ x = z) :
    Additive.ofMul (sphericalFace τ hτ 0).homotopyClassStick -
      Additive.ofMul (sphericalFace τ hτ 1).homotopyClassStick +
      Additive.ofMul (sphericalFace τ hτ 2).homotopyClassStick -
      Additive.ofMul (sphericalFace τ hτ 3).homotopyClassStick +
      Additive.ofMul (sphericalFace τ hτ 4).homotopyClassStick =
        (0 : Additive (HomotopyGroup.Pi 3 Z z)) := by
  have h := spherical_signed_homotopy_addition τ hτ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

/-- Cube edges map into the actual tetrahedral edge skeleton. -/
theorem tetrahedral_edge_skeleton (x : Fin 3 → I)
    (hx : x ∈ cubeCodimTwoBoundary (Fin 3)) :
    Cube.stickBreaking 3 x ∈ simplexSkeleton 2 3 :=
  Cube.stickBreaking_codimTwo_mem_skeleton x hx

end QuillenTest.SphericalHomotopyAddition
