/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.LocalCoefficients.SecondHurewicz

/-! Actual three-prism chains for paired triangle homotopies. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Convexity
open scoped Simplicial
namespace Quillen.LocalCoefficients.TrianglePrismComparison
open SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y]
  {a b c d : SingularSimplex Y ⦋2⦌}

/-- The actual simplex homotopy, with only its domain lifted to the coefficient universe. -/
def lifted (H : a.Homotopy b) :
    (a.comp ⟨ULift.down, continuous_uliftDown⟩).Homotopy
      (b.comp ⟨ULift.down, continuous_uliftDown⟩) :=
  H.compContinuousMap ⟨ULift.down, continuous_uliftDown⟩

/-- The three original tetrahedra of a triangle homotopy. -/
def triangle (H : a.Homotopy b) (i : Fin 3) : SingularSimplex Y ⦋3⦌ :=
  prismSimplex (lifted H) i (triangleUp :
    SingularSimplex (ULift.{u} (StdSimplex ℝ (Fin 3))) ⦋2⦌)

/-- The two original triangular prisms on a displayed boundary edge. -/
def side (H : a.Homotopy b) (i : Fin 2) (j : Fin 3) : SingularSimplex Y ⦋2⦌ :=
  prismSimplex (lifted H) i
    (restrictSimplex (triangleUp :
      SingularSimplex (ULift.{u} (StdSimplex ℝ (Fin 3))) ⦋2⦌) (SimplexCategory.δ j))

/-- The literal alternating three-prism chain for the actual homotopy. -/
def chain (H : a.Homotopy b) : (Chains Y).X 3 :=
  simplexChain (triangle H 0) - simplexChain (triangle H 1) + simplexChain (triangle H 2)

/-- The boundary retains all six side triangles and both original endpoints. -/
theorem chain_boundary (H : a.Homotopy b) :
    (Chains Y).d 3 2 (chain H) = simplexChain b - simplexChain a -
      (simplexChain (side H 0 0) - simplexChain (side H 1 0)) +
      (simplexChain (side H 0 1) - simplexChain (side H 1 1)) -
      (simplexChain (side H 0 2) - simplexChain (side H 1 2)) := by
  have hfirst : restrictSimplex (triangle H 0) (SimplexCategory.δ 0) = b :=
    prismSimplex_face_zero (lifted H) triangleUp
  have hlast : restrictSimplex (triangle H 2) (SimplexCategory.δ 3) = a :=
    prismSimplex_face_last (lifted H) triangleUp
  have hm0 : restrictSimplex (triangle H 0) (SimplexCategory.δ 1) =
      restrictSimplex (triangle H 1) (SimplexCategory.δ 1) :=
    (prismSimplex_middle_face (lifted H) (0 : Fin 2) triangleUp).symm
  have hm1 : restrictSimplex (triangle H 1) (SimplexCategory.δ 2) =
      restrictSimplex (triangle H 2) (SimplexCategory.δ 2) :=
    (prismSimplex_middle_face (lifted H) (1 : Fin 2) triangleUp).symm
  have h02 : restrictSimplex (triangle H 0) (SimplexCategory.δ 2) = side H 0 1 :=
    prismSimplex_face_of_lt (lifted H) (1 : Fin 3) (0 : Fin 2) (by decide) triangleUp
  have h03 : restrictSimplex (triangle H 0) (SimplexCategory.δ 3) = side H 0 2 :=
    prismSimplex_face_of_lt (lifted H) (2 : Fin 3) (0 : Fin 2) (by decide) triangleUp
  have h10 : restrictSimplex (triangle H 1) (SimplexCategory.δ 0) = side H 0 0 :=
    prismSimplex_face_of_le (lifted H) (0 : Fin 3) (0 : Fin 2) (by decide) triangleUp
  have h13 : restrictSimplex (triangle H 1) (SimplexCategory.δ 3) = side H 1 2 :=
    prismSimplex_face_of_lt (lifted H) (2 : Fin 3) (1 : Fin 2) (by decide) triangleUp
  have h20 : restrictSimplex (triangle H 2) (SimplexCategory.δ 0) = side H 1 0 :=
    prismSimplex_face_of_le (lifted H) (0 : Fin 3) (1 : Fin 2) (by decide) triangleUp
  have h21 : restrictSimplex (triangle H 2) (SimplexCategory.δ 1) = side H 1 1 :=
    prismSimplex_face_of_le (lifted H) (1 : Fin 3) (1 : Fin 2) (by decide) triangleUp
  rw [chain, map_add, map_sub, tetrahedron_boundary, tetrahedron_boundary,
    tetrahedron_boundary, hfirst, hlast, hm0, hm1, h02, h03, h10, h13, h20, h21]
  abel

/-- Equal WHOLE edge homotopies give equal actual side-prism simplices. -/
theorem side_eq (H : a.Homotopy b) (K : c.Homotopy d) (j k : Fin 3)
    (h : ∀ s (x : StdSimplex ℝ (Fin 2)), H (s, x.map (SimplexCategory.δ j)) =
      K (s, x.map (SimplexCategory.δ k))) (i : Fin 2) : side H i j = side K i k := by
  ext z
  rw [side, side, prismSimplex_apply, prismSimplex_apply]
  exact h _ _

/-- Opposite-edge pairing cancels every side prism, preserving the original endpoint chains. -/
theorem paired_chain_boundary (H : a.Homotopy b) (K : c.Homotopy d)
    (h02 : ∀ s (x : StdSimplex ℝ (Fin 2)), H (s, x.map (SimplexCategory.δ 0)) =
      K (s, x.map (SimplexCategory.δ 2)))
    (h11 : ∀ s (x : StdSimplex ℝ (Fin 2)), H (s, x.map (SimplexCategory.δ 1)) =
      K (s, x.map (SimplexCategory.δ 1)))
    (h20 : ∀ s (x : StdSimplex ℝ (Fin 2)), H (s, x.map (SimplexCategory.δ 2)) =
      K (s, x.map (SimplexCategory.δ 0))) :
    (Chains Y).d 3 2 (chain H - chain K) =
      (simplexChain b - simplexChain d) - (simplexChain a - simplexChain c) := by
  rw [map_sub, chain_boundary, chain_boundary,
    side_eq H K 0 2 h02 0, side_eq H K 0 2 h02 1,
    side_eq H K 1 1 h11 0, side_eq H K 1 1 h11 1,
    side_eq H K 2 0 h20 0, side_eq H K 2 0 h20 1]
  abel

end Quillen.LocalCoefficients.TrianglePrismComparison
