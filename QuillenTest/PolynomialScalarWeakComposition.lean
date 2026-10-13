/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarWeakComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # The original polynomial scalar factorization and its weak-composition consumers -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Convexity
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Scheme.PolynomialLaurent
open scoped Simplicial Topology
universe u
namespace QuillenTest.PolynomialScalarWeakComposition

open Quillen
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The actual factorization triangle retains independent object and nerve coordinates. -/
theorem original_apply
    (t : StdSimplex ℝ (Fin 2)) (z : StdSimplex ℝ (Fin 3)) :
    perfectScalarWeakComposition (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (t, z) =
      (perfectOpenNested (laurentPlus R)).coarse.weakObjectCompositionRealization
        (perfectScalarInclusion (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R) K)
        (perfectScalarProjection (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R) K)
        (perfectScalarInclusion_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)
        ((perfectOpenNested (laurentPlus R)).le_weq _
          (perfectScalarProjection_weak (Spec (.of (Polynomial R)))
            (polynomialGlobalCoordinate R) K)) (t, z) :=
  perfectScalarWeakComposition_apply (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K t z

/-- The first nerve edge is the entire original scalar-cofibration square. -/
theorem original_inclusion (t z : StdSimplex ℝ (Fin 2)) :
    perfectScalarWeakComposition (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (t, z.map (SimplexCategory.δ 2)) =
      bisimplexRealization (perfectOpenNested (laurentPlus R)).coarse
        ((perfectOpenNested (laurentPlus R)).coarse.weakObjectSimplex
          (perfectScalarInclusion (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R) K)
          (perfectScalarInclusion_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectOpenNested (laurentPlus R)).coarse.weakObjectSimplex
            (perfectScalarInclusion (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R) K)
            (perfectScalarInclusion_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
              (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)).property)
        (t, z) :=
  perfectScalarWeakComposition_inclusion (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K t z

/-- The second nerve edge retains the unchanged fine weak projection. -/
theorem original_projection (t z : StdSimplex ℝ (Fin 2)) :
    perfectScalarWeakComposition (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (t, z.map (SimplexCategory.δ 0)) =
      bisimplexRealization (perfectOpenNested (laurentPlus R)).coarse
        ((perfectOpenNested (laurentPlus R)).coarse.weakObjectSimplex
          (perfectScalarProjection (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R) K)
          ((perfectOpenNested (laurentPlus R)).le_weq _
            (perfectScalarProjection_weak (Spec (.of (Polynomial R)))
              (polynomialGlobalCoordinate R) K))).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          ((perfectOpenNested (laurentPlus R)).coarse.weakObjectSimplex
            (perfectScalarProjection (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R) K)
            ((perfectOpenNested (laurentPlus R)).le_weq _
              (perfectScalarProjection_weak (Spec (.of (Polynomial R)))
                (polynomialGlobalCoordinate R) K))).property) (t, z) :=
  perfectScalarWeakComposition_projection (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K t z

/-- The long edge is multiplication by the original forward polynomial coordinate. -/
theorem original_scalar (t z : StdSimplex ℝ (Fin 2)) :
    perfectScalarWeakComposition (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (t, z.map (SimplexCategory.δ 1)) =
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
        (t, z) :=
  perfectScalarWeakComposition_scalar (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K t z

/-- The actual localization map carries the entire fine projection square to its prescribed face. -/
theorem original_projection_fine (t z : StdSimplex ℝ (Fin 2)) :
    changeWeakMap (perfectOpenNested (laurentPlus R))
        (bisimplexRealization (perfectWaldhausen (Spec (.of (Polynomial R))))
          ((perfectWaldhausen (Spec (.of (Polynomial R)))).weakObjectSimplex
            (perfectScalarProjection (Spec (.of (Polynomial R))) (polynomialGlobalCoordinate R) K)
            (perfectScalarProjection_weak (Spec (.of (Polynomial R)))
              (polynomialGlobalCoordinate R) K)).val
          ((isSimplex₂_diagonal_iff _ _ _).mpr
            ((perfectWaldhausen (Spec (.of (Polynomial R)))).weakObjectSimplex
              (perfectScalarProjection (Spec (.of (Polynomial R)))
                (polynomialGlobalCoordinate R) K)
              (perfectScalarProjection_weak (Spec (.of (Polynomial R)))
                (polynomialGlobalCoordinate R) K)).property) (t, z)) =
      perfectScalarWeakComposition (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (t, z.map (SimplexCategory.δ 0)) :=
  perfectScalarWeakComposition_projection_fine (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K t z

end QuillenTest.PolynomialScalarWeakComposition
