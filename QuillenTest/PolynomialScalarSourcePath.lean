/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSourcePath
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # The prescribed fine polynomial-cofiber source path -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry unitInterval
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Scheme.PolynomialLaurent
open scoped Topology
universe u
namespace QuillenTest.PolynomialScalarSourcePath

open Quillen
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The source is literally the original object loop followed by its categorical-cofiber loop. -/
theorem original_source (t : unitInterval) :
    perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K (0, t) =
      (((perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop K).trans
        ((perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop
          ((ExtensionCategory.cofiber (perfectWaldhausen (Spec (.of (Polynomial R))))).obj
            (perfectScalarExtension _ (polynomialGlobalCoordinate R) K)))) t :=
  (perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K).apply_zero t

/-- The terminal loop is the unchanged original source object loop. -/
theorem original_target (t : unitInterval) :
    perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K (1, t) =
      (perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop K t :=
  (perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K).apply_one t

/-- Both based endpoints remain fixed throughout the prescribed fine path. -/
theorem original_based_endpoints (s : unitInterval) :
    perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K (s, 0) =
        (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint ∧
      perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K (s, 1) =
        (perfectWaldhausen (Spec (.of (Polynomial R)))).kBasepoint :=
  ⟨Path.Homotopy.source _ s, Path.Homotopy.target _ s⟩

/-- The original fine projection square survives localization at every independent time. -/
theorem original_projection_image (s t : unitInterval) :
    changeWeakMap (perfectOpenNested (laurentPlus R))
        (perfectScalarProjectionObjectTrack _ (polynomialGlobalCoordinate R) K (s, t)) =
      (perfectOpenNested (laurentPlus R)).coarse.weakObjectSquareTrack
        (perfectScalarProjection _ (polynomialGlobalCoordinate R) K)
        ((perfectOpenNested (laurentPlus R)).le_weq _
          (perfectScalarProjection_weak _ (polynomialGlobalCoordinate R) K)) (s, t) :=
  perfectScalarProjectionObjectTrack_changeWeak _ _ _ _ _

/-- The first half is the specified face of the actual forward-T cofiber prism. -/
theorem original_first_half (s t : unitInterval) (h : (s : ℝ) ≤ 1 / 2) :
    changeWeakMap (perfectOpenNested (laurentPlus R))
        (perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K (s, t)) =
      perfectOpenScalarCofiberCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩, 1, t) := by
  rw [perfectScalarCofiberSourceTrack_changeWeak (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R), dite_eq_left h]

/-- The second half is the original projection square with its prescribed rescaled time. -/
theorem original_second_half (s t : unitInterval) (h : ¬ (s : ℝ) ≤ 1 / 2) :
    changeWeakMap (perfectOpenNested (laurentPlus R))
        (perfectScalarCofiberSourceTrack _ (polynomialGlobalCoordinate R) K (s, t)) =
      (perfectOpenNested (laurentPlus R)).coarse.weakObjectSquareTrack
        (perfectScalarProjection _ (polynomialGlobalCoordinate R) K)
        ((perfectOpenNested (laurentPlus R)).le_weq _
          (perfectScalarProjection_weak _ (polynomialGlobalCoordinate R) K))
        (⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩, t) := by
  rw [perfectScalarCofiberSourceTrack_changeWeak (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R), dite_eq_right h]

end QuillenTest.PolynomialScalarSourcePath
