/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberPrism
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # The original polynomial scalar factorization and its actual cofiber-prism consumers -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry unitInterval
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Scheme.PolynomialLaurent
open scoped Topology
universe u
namespace QuillenTest.PolynomialScalarCofiberPrism

open Quillen
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))

/-- The original two factors retain literal multiplication by the polynomial coordinate. -/
theorem original_scalar_factorization :
    perfectScalarInclusion _ (polynomialGlobalCoordinate R) K ≫
        perfectScalarProjection _ (polynomialGlobalCoordinate R) K =
      (perfectGlobalScalar _ (polynomialGlobalCoordinate R)).app K :=
  perfectScalarInclusion_projection _ _ _

/-- The original first factor is weak after the actual Laurent open, with no supplied weakness. -/
theorem original_laurent_weak_inclusion :
    (perfectOpenNested (laurentPlus R)).coarse.weq
      (perfectScalarInclusion _ (polynomialGlobalCoordinate R) K) :=
  perfectScalarInclusion_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K

/-- Restriction retains the actual forward Laurent-coordinate unit on every original complex. -/
theorem original_restricted_unit :
    (restrict (laurentPlus R)).map
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K.obj) =
      (complexGlobalUnitIso _ (laurentGlobalUnit R)).hom.app
        ((restrict (laurentPlus R)).obj K.obj) :=
  restrict_map_complexGlobalScalar_unit (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K.obj

/-- The full scalar cube keeps its original comparison, nerve and loop coordinates. -/
theorem original_three_parameters (a s t : unitInterval) :
    perfectOpenScalarCofiberCompositionLoops (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, s) t =
      perfectOpenScalarCofiberCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (a, s, t) :=
  perfectOpenScalarCofiberCompositionLoops_apply _ _ _ _ _ _ _ _

/-- The translated face uses the actual cofiber's fiber path, with its full reversed time. -/
theorem original_translated_cofiber (t s : unitInterval) :
    perfectOpenScalarCofiberCompositionCube (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K
        (0, unitInterval.symm s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        (perfectOpenNested (laurentPlus R)).coarse.kZeroObjectLoop K
          ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop (perfectOpenNested (laurentPlus R))
          (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)
          ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s :=
  perfectOpenScalarCofiberCompositionCube_zero _ _ _ _ _ _ _

/-- The same original quotient reaches the literal cone through its specified sign map. -/
theorem original_signed_quotient :
    (ExtensionCategory.quotient (perfectWaldhausen (Spec (.of (Polynomial R))))).app
        (perfectScalarExtension _ (polynomialGlobalCoordinate R) K) ≫
      (perfectOpenScalarCofiberIso (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).hom =
      (locallyPerfect (Spec (.of (Polynomial R)))).homMk
        (SplitFactorization.quotientToCone
          ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K.obj)) :=
  perfectOpenScalarCofiberIso_quotient _ _ _ _ _

end QuillenTest.PolynomialScalarCofiberPrism
