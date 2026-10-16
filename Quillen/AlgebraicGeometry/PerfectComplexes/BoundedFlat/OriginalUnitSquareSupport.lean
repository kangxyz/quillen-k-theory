/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquareSimplex
public import Quillen.Topology.Path.ParameterBoundarySupport

/-! Exact primitive support of the original geometric unit square. Its rotation, cancellation,
constant-half contraction, and three-side quotient use only the six original triangles.
Only those triangles must be ordered when the complete surface is transferred to a new family. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.ParameterSupport
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.OriginalUnitSquareSupport
open OriginalUnitSquareSimplex

/-- The six unchanged primitive triangles, in their original local order. -/
def face : Fin 6 → (⦋2⦌ ⟶ ⦋7⦌) :=
  ![triangleFace 0 1 2 (by decide) (by decide),
    triangleFace 2 3 7 (by decide) (by decide),
    triangleFace 0 2 7 (by decide) (by decide),
    triangleFace 0 4 5 (by decide) (by decide),
    triangleFace 5 6 7 (by decide) (by decide),
    triangleFace 0 5 7 (by decide) (by decide)]

/-- The union consists of the actual images of the six complete parameter triangles. -/
def support : Set (StdSimplex ℝ (Fin 8)) :=
  {z | ∃ (i : Fin 6) (w : StdSimplex ℝ (Fin 3)),
    StdSimplex.map (face i).toOrderHom w = z}

theorem triangle_in (i : Fin 6) : HomotopyIn support (triangle (face i)) :=
  fun z ↦ ⟨i, Quillen.TheoremB.compositionTriangleHomotopy z, rfl⟩

/-- Both split unit routes and their normalized comparison stay in the six primitive faces. -/
theorem routes_in : HomotopyIn support routesParameter :=
  hom_trans (hom_symm (hom_hcomp (triangle_in 0) (triangle_in 1)))
    (hom_trans (hom_trans (hom_symm (triangle_in 2)) (triangle_in 5))
      (hom_hcomp (triangle_in 3) (triangle_in 4)))

/-- The original eight-stage rotation and terminal contraction introduce no new scalar values. -/
theorem rotated_in : HomotopyIn support rotatedParameter :=
  hom_trans (rotate_in routes_in)
    (hom_hcomp (hom_symm (hom_transRefl (hom_target (triangle_in 1))))
      (hom_refl (path_symm (hom_target (triangle_in 4)))))

/-- Every point of the entire original square is on one of its six unchanged triangles. -/
theorem square_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 6) (w : StdSimplex ℝ (Fin 3)),
      StdSimplex.map (face i).toOrderHom w = squareParameter z :=
  collapsed_in rotated_in z

/-- The entire left side is the original right-unit path at its unchanged speed. -/
theorem square_left_path (r : unitInterval) : squareParameter (r, 0) = rightUnitPath r :=
  collapsed_left_path rotatedParameter r

/-- The entire right side is the original left-unit path at its unchanged speed. -/
theorem square_right_path (r : unitInterval) : squareParameter (r, 1) = leftUnitPath r :=
  collapsed_right_path rotatedParameter r

/-- The original terminal identity track is the literal final vertex for every path time. -/
theorem square_top_path (t : unitInterval) :
    squareParameter (1, t) = (StdSimplex.single 7 : StdSimplex ℝ (Fin 8)) :=
  collapsed_top_path rotatedParameter t

variable {k : ℕ} (f : Fin 8 → Fin (k + 1))

/-- Only the original triangle supports need to preserve order under a relabeling. -/
def imageFace (h : ∀ i, Monotone (f ∘ (face i).toOrderHom)) (i : Fin 6) :
    ⦋2⦌ ⟶ ⦋k⦌ :=
  SimplexCategory.Hom.mk ⟨f ∘ (face i).toOrderHom, h i⟩

/-- Exact face preservation on the six primitive supports preserves every native square value.
The relabeling need not preserve the unrelated cross-branch vertex order. -/
theorem square_transfer {V W : Model.{u}} (S : ModelSimplex V W 7)
    (T : ModelSimplex V W k) (h : ∀ i, Monotone (f ∘ (face i).toOrderHom))
    (hf : ∀ i, T.face (imageFace f h i) = S.face (face i))
    (n : ℕ) (z : unitInterval × unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily T n (StdSimplex.map f (squareParameter z), x) =
      prespectrumSimplexFamily S n (squareParameter z, x) := by
  obtain ⟨i, w, hw⟩ := square_support z
  rw [← hw, ← StdSimplex.map_comp]
  change prespectrumSimplexFamily T n (StdSimplex.map (imageFace f h i).toOrderHom w, x) = _
  rw [prespectrumSimplexFamily_face, hf, prespectrumSimplexFamily_face]

end Quillen.PerfectComplexes.OriginalUnitSquareSupport
