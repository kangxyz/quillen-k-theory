/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberChangeWeak
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # The original fine scalar-cofiber track and its exact localization image -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.Waldhausen Quillen.Waldhausen.Fibration AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Topology
universe u
namespace QuillenTest.PolynomialScalarFineCofiberTrack

open Quillen
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The fine source is the original source loop followed by the actual categorical-cofiber loop. -/
theorem original_fine_source (t : unitInterval) :
    perfectScalarCofiberObjectTrack _ (polynomialGlobalCoordinate R) K (0, t) =
      (((perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop K).trans
        ((perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop
          ((ExtensionCategory.cofiber (perfectWaldhausen (Spec (.of (Polynomial R))))).obj
            (perfectScalarExtension _ (polynomialGlobalCoordinate R) K)))) t :=
  (perfectScalarCofiberObjectTrack _ (polynomialGlobalCoordinate R) K).apply_zero t

/-- The fine target is the loop of the unchanged factorization middle object. -/
theorem original_fine_target (t : unitInterval) :
    perfectScalarCofiberObjectTrack _ (polynomialGlobalCoordinate R) K (1, t) =
      (perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop
        ((ExtensionCategory.middle (perfectWaldhausen (Spec (.of (Polynomial R))))).obj
          (perfectScalarExtension _ (polynomialGlobalCoordinate R) K)) t :=
  (perfectScalarCofiberObjectTrack _ (polynomialGlobalCoordinate R) K).apply_one t

/-- The original localization map retains the full fine track as the prescribed prism face. -/
theorem original_localized_face (a t : unitInterval) :
    changeWeakMap (perfectOpenNested (laurentPlus R))
        (perfectScalarCofiberObjectTrack _ (polynomialGlobalCoordinate R) K (a, t)) =
      perfectOpenScalarCofiberCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, 1, t) :=
  perfectScalarCofiberObjectTrack_prism_face _ _ _ _ _ _ _

/-- Both fine based endpoints remain fixed for every independent comparison time. -/
theorem original_based_endpoints (a : unitInterval) :
    perfectScalarCofiberObjectTrack _ (polynomialGlobalCoordinate R) K (a, 0) =
        (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint ∧
      perfectScalarCofiberObjectTrack _ (polynomialGlobalCoordinate R) K (a, 1) =
        (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint :=
  ⟨Path.Homotopy.source _ a, Path.Homotopy.target _ a⟩

end QuillenTest.PolynomialScalarFineCofiberTrack
