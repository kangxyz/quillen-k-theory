/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.BarycentricTermMesh
public import Mathlib.Tactic.NormNum

/-! # Nontrivial consumers of genuine barycentric simplex geometry -/

@[expose] public section

noncomputable section

open Convexity
open Quillen.BarycentricSubdivision
open scoped Topology

namespace Quillen.Tests.BarycentricGeometry

/-- The triangle flag starts at its first genuine vertex. -/
theorem triangle_first_vertex :
    simplexMap (Equiv.refl (Fin 3)) (StdSimplex.single 0) = StdSimplex.single 0 := by
  rw [simplexMap_single]
  have hface : face (Equiv.refl (Fin 3)) 0 = {0} := by decide
  simp [vertex, hface]

/-- The last vertex of the triangle flag is the triangle's actual barycenter. -/
theorem triangle_last_coordinates (j : Fin 3) :
    (simplexMap (Equiv.refl (Fin 3)) (StdSimplex.single 2)).weights j = 1 / 3 := by
  rw [simplexMap_single]
  have hface : face (Equiv.refl (Fin 3)) 2 = Finset.univ := by decide
  simp [vertex, hface, StdSimplex.weights_subBarycenter, Finsupp.single_apply]

/-- A nontrivial permutation really changes the first flag vertex. -/
theorem triangle_swapped_first :
    simplexMap (Equiv.swap (0 : Fin 3) 2) (StdSimplex.single 0) =
      StdSimplex.single 2 := by
  rw [simplexMap_single]
  have hface : face (Equiv.swap (0 : Fin 3) 2) 0 = {2} := by decide
  simp [vertex, hface]

/-- The sharp triangle contraction factor is two thirds. -/
theorem triangle_contraction : contractionFactor 2 = 2 / 3 := by
  norm_num [contractionFactor]

/-- Arbitrary repeated triangle flags satisfy a genuine quantitative mesh bound. -/
theorem triangle_two_stage_mesh (p q : Equiv.Perm (Fin 3))
    (x y : StdSimplex ℝ (Fin 3)) :
    l1Dist (iteratedSimplexMap [p, q] x) (iteratedSimplexMap [p, q] y) ≤ 8 / 9 := by
  have h := l1Dist_iteratedSimplexMap_le_mesh [p, q] x y
  norm_num [triangle_contraction] at h ⊢
  exact h

/-- A continuous, nonconstant singular triangle. -/
def coordinateTriangle : C(StdSimplex ℝ (Fin 3), ℝ) :=
  ⟨fun x ↦ x.weights 0, StdSimplex.continuous_weights_apply ℝ (0 : Fin 3)⟩

/-- A proper two-set open cover, neither member containing the original image. -/
def twoCover (b : Bool) : Set ℝ := if b then Set.Iio (3 / 4) else Set.Ioi (1 / 4)

theorem twoCover_open (b : Bool) : IsOpen (twoCover b) := by
  cases b <;> simp [twoCover, isOpen_Ioi, isOpen_Iio]

theorem twoCover_covers (x : ℝ) : ∃ b, x ∈ twoCover b := by
  by_cases h : x < 3 / 4
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    change 1 / 4 < x
    linarith

/-- The original triangle genuinely crosses this cover. -/
theorem coordinateTriangle_not_small :
    ¬ ∃ b, Set.range coordinateTriangle ⊆ twoCover b := by
  rintro ⟨b, hb⟩
  cases b
  · have h := hb (Set.mem_range_self (StdSimplex.single (1 : Fin 3)))
    norm_num [coordinateTriangle, twoCover, StdSimplex.weights_single] at h
  · have h := hb (Set.mem_range_self (StdSimplex.single (0 : Fin 3)))
    norm_num [coordinateTriangle, twoCover, StdSimplex.weights_single] at h

/-- Nevertheless, one common finite depth makes every actual subdivision
triangle small for the same proper cover. -/
theorem coordinateTriangle_eventually_small :
    ∃ k : ℕ, ∀ ps : List (Equiv.Perm (Fin 3)), ps.length = k →
      ∃ b, Set.range (coordinateTriangle.comp (iteratedSimplexMap ps)) ⊆ twoCover b :=
  exists_iteratedSimplexMap_cover_small coordinateTriangle twoCover
    twoCover_open twoCover_covers

/-- The face-composition formula works for a nonconstant triangle edge. -/
theorem triangle_edge_restriction (v : Fin 3 → StdSimplex ℝ (Fin 4))
    (x : StdSimplex ℝ (Fin 2)) :
    affineSimplex v (StdSimplex.map (Fin.succAbove (1 : Fin 3)) x) =
      affineSimplex (v ∘ Fin.succAbove (1 : Fin 3)) x :=
  affineSimplex_map v _ x

/-- A concrete descending triangle term of recursive coning. -/
def descendingTriangle : SubdivisionSimplex 2 :=
  ⟨[listBarycenter (standardVertices 2),
      listBarycenter [StdSimplex.single 0, StdSimplex.single 1],
      listBarycenter [StdSimplex.single 0]], by
    apply SubdivisionListChains.SubdivisionTerm.cons (standardVertices 2)
      (by simp [standardVertices]) (2 : Fin 3)
    change SubdivisionListChains.SubdivisionTerm listBarycenter
      [StdSimplex.single 0, StdSimplex.single 1] _
    apply SubdivisionListChains.SubdivisionTerm.cons
      [StdSimplex.single (0 : Fin 3), StdSimplex.single 1] (by simp) (1 : Fin 2)
    change SubdivisionListChains.SubdivisionTerm listBarycenter
      [StdSimplex.single (0 : Fin 3)] _
    apply SubdivisionListChains.SubdivisionTerm.cons
      [StdSimplex.single (0 : Fin 3)] (by simp) (0 : Fin 1)
    exact SubdivisionListChains.SubdivisionTerm.nil⟩

/-- Its actual continuous affine realization has the quantitative mesh bound. -/
theorem descending_triangle_mesh (x y : StdSimplex ℝ (Fin 3)) :
    l1Dist (subdivisionTermMap descendingTriangle x)
      (subdivisionTermMap descendingTriangle y) ≤ 2 / 3 * l1Dist x y := by
  simpa [triangle_contraction] using l1Dist_subdivisionTermMap_le descendingTriangle x y

/-- The constructed recursive chain, not merely a chosen family of flags,
is supported on the exact terms used in the mesh theorem. -/
theorem triangle_recursive_support :
    SubdivisionListChains.Supported
      (SubdivisionListChains.SubdivisionTerm listBarycenter (standardVertices 2))
      (SubdivisionListChains.subdivision listBarycenter
        (SubdivisionListChains.generator (standardVertices 2))) :=
  SubdivisionListChains.subdivision_supported_terms _ _

/-- All iterates of actual recursive terms become small in a proper open cover
which the original singular triangle crosses. -/
theorem coordinateTriangle_recursive_eventually_small :
    ∃ k : ℕ, ∀ ps : List (SubdivisionSimplex 2), ps.length = k →
      ∃ b, Set.range (coordinateTriangle.comp (iteratedTermMap ps)) ⊆ twoCover b :=
  exists_iteratedTermMap_cover_small coordinateTriangle twoCover twoCover_open twoCover_covers

end Quillen.Tests.BarycentricGeometry
