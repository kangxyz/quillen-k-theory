/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarWeakCompositionCube
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # Original composition-cube faces and scalar/cofiber pasting consumers -/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry Convexity unitInterval
open Quillen.PerfectComplexes.Affine
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Simplicial Topology
universe u v
namespace QuillenTest.PolynomialScalarCompositionCube

open Quillen

section Generic
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- The terminal comparison retains the original composite arrow at both square coordinates. -/
theorem original_composite_face (s t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (1, s, t) =
      bisimplexRealization W
        (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) :=
  W.weakObjectCompositionCube_one f g hf hg s t

/-- The actual whole vertex triangle is the chosen basepoint, independently of its nerve point. -/
theorem original_zero_vertices (e : Fin 2) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (StdSimplex.single e, z) = W.kBasepoint :=
  W.weakObjectCompositionRealization_vertex f g hf hg e z

/-- The full generic square consists of actual based loops with three independent times. -/
theorem original_based_coordinates (a s t : unitInterval) :
    W.weakObjectCompositionLoops f g hf hg (a, s) t =
      W.weakObjectCompositionCube f g hf hg (a, s, t) :=
  W.weakObjectCompositionLoops_apply f g hf hg a s t

end Generic

variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The actual scalar square retains its comparison, nerve and object-loop coordinates. -/
theorem original_scalar_coordinates (a s t : unitInterval) :
    perfectScalarWeakCompositionLoops (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, s) t =
      perfectScalarWeakCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, s, t) :=
  perfectScalarWeakCompositionLoops_apply _ _ _ _ _ _ _ _

/-- The first half is the original cofiber-prism face with exact rescaled nerve time. -/
theorem original_shared_cofiber_face (s t : unitInterval) (h : (s : ℝ) ≤ 1 / 2) :
    perfectScalarWeakCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (0, s, t) =
      perfectOpenScalarCofiberCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (1, ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩, t) :=
  perfectScalarWeakCompositionCube_shared_face _ _ _ _ _ _ _ h

/-- The long nerve edge remains the entire original forward polynomial-scalar square. -/
theorem original_scalar_face (s t : unitInterval) :
    perfectScalarWeakCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (1, s, t) =
      bisimplexRealization (perfectOpenNested (laurentPlus R)).coarse
        ((perfectOpenNested (laurentPlus R)).coarse.weakObjectSimplex
          ((perfectGlobalScalar (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R)).app K)
          (perfectGlobalScalar_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectOpenNested (laurentPlus R)).coarse.weakObjectSimplex
            ((perfectGlobalScalar (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R)).app K)
            (perfectGlobalScalar_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
              (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) :=
  perfectScalarWeakCompositionCube_one _ _ _ _ _ _ _

end QuillenTest.PolynomialScalarCompositionCube
