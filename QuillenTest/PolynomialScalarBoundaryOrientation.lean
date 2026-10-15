/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberBoundaryOrientation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-!
# The original polynomial-cofiber loop and its prescribed orientation

These consumers keep the actual iterated localization fiber, the fine return path and all
three homotopy coordinates. The terminal formula reverses the parameter of the original
forward-T scalar square; it does not replace that scalar by an unproved inverse-action model.
-/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.PerfectComplexes.Affine
open Quillen.Waldhausen.Fibration AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Topology
universe u
namespace QuillenTest.PolynomialScalarBoundaryOrientation

open Quillen
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The original iterated fiber keeps the fine source-plus-categorical-cofiber object loop. -/
theorem original_iterated_source :
    (perfectScalarCofiberIteratedFiber (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).val.1.val.1 =
      (((perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop K).trans
        ((perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop
          ((ExtensionCategory.cofiber (perfectWaldhausen (Spec (.of (Polynomial R))))).obj
            (perfectScalarExtension _ (polynomialGlobalCoordinate R) K)))) := rfl

/-- The return coordinate is exactly the fine cofiber triangle followed by the fine projection. -/
theorem original_fine_return (s t : unitInterval) :
    (perfectScalarCofiberIteratedFiber (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).val.2 s t =
      perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K (s, t) := rfl

/-- The comparison begins at the unchanged loop produced by the original iterated-fiber map. -/
theorem original_orientation_source (s t : unitInterval) :
    perfectScalarCofiberBoundaryOrientation (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (0, s) t =
      perfectScalarCofiberBoundaryLoop (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K s t :=
  congrArg (fun p ↦ p t)
    ((perfectScalarCofiberBoundaryOrientation (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).apply_zero s)

/-- The endpoint is the reversed nerve parameter of the original forward-T scalar square. -/
theorem original_forward_scalar_reversed (s t : unitInterval) :
    perfectScalarCofiberBoundaryOrientation (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (1, s) t =
      bisimplexRealization (perfectOpenNested (laurentPlus R)).coarse
        (((perfectOpenNested (laurentPlus R)).coarse).weakObjectSimplex
          ((perfectGlobalScalar _ (polynomialGlobalCoordinate R)).app K)
          (perfectGlobalScalar_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          (((perfectOpenNested (laurentPlus R)).coarse).weakObjectSimplex
            ((perfectGlobalScalar _ (polynomialGlobalCoordinate R)).app K)
            (perfectGlobalScalar_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
              (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm (unitInterval.symm s)) :=
  congrArg (fun p ↦ p t)
    ((perfectScalarCofiberBoundaryOrientation (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).apply_one s)

/-- The object-loop component stays fixed at both ends for every comparison and loop time. -/
theorem original_component_endpoints (a t : unitInterval) :
    perfectScalarCofiberBoundaryOrientation (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, 0) t =
        (perfectOpenNested (laurentPlus R)).coarse.kZeroObjectLoop K t ∧
      perfectScalarCofiberBoundaryOrientation (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, 1) t =
        (perfectOpenNested (laurentPlus R)).coarse.kZeroObjectLoop K t :=
  ⟨congrArg (fun p : Path (perfectOpenNested (laurentPlus R)).coarse.kBasepoint
      (perfectOpenNested (laurentPlus R)).coarse.kBasepoint ↦ p t)
      (Path.Homotopy.source _ a),
    congrArg (fun p : Path (perfectOpenNested (laurentPlus R)).coarse.kBasepoint
      (perfectOpenNested (laurentPlus R)).coarse.kBasepoint ↦ p t)
      (Path.Homotopy.target _ a)⟩

/-- The unchanged original loop has the reversed scalar-square path class
in its actual object-loop component. -/
theorem original_path_class :
    Path.Homotopic.Quotient.mk
        (perfectScalarCofiberBoundaryLoop (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K) =
      Path.Homotopic.Quotient.mk
        (perfectScalarWeakLoop (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).symm :=
  Quotient.sound ⟨perfectScalarCofiberBoundaryOrientation (laurentPlus R)
    (polynomialGlobalCoordinate R) (laurentGlobalUnit R)
    (polynomialGlobalCoordinate_laurentPlus R) K⟩

end QuillenTest.PolynomialScalarBoundaryOrientation
