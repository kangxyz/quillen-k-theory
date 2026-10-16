/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneInversion
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates
public import Mathlib.Data.ZMod.Basic

/-!
The negative polynomial scalar restricts through the original, canonically rebased K-map to
the inverse of the forward Laurent class. The rank-one consumer keeps the actual structure
sheaf restriction isomorphism; no nonzero-ring assumption is present.
-/
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.GlobalUnitKOneInversion

/-- The negative-chart scalar and forward Laurent class cancel after actual restriction. -/
theorem negative_scalar_restrict (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    perfectOpenKRestrict (laurentMinus R) 1
        (perfectScalarForwardKOneClass (laurentMinus R) K (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_laurentMinus R)) *
      perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
        ((perfectRestrict (laurentMinus R)).obj K) = 1 := by
  rw [perfectScalarForwardKOneClass_restrict_inv]
  exact inv_mul_cancel _

/-- Rank one uses the canonical structure-sheaf isomorphism after the original zero rebase. -/
private theorem negative_scalar_restrict_rankOne (R : CommRingCat.{u}) :
    perfectOpenKRestrict (laurentMinus R) 1
        (perfectScalarForwardKOneClass (laurentMinus R)
          (rankOnePerfect (Spec (.of (Polynomial R)))) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_laurentMinus R)) =
      (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
        (rankOnePerfect (Spec (.of (LaurentPolynomial R)))))⁻¹ := by
  rw [perfectScalarForwardKOneClass_restrict_rankOne, perfectGlobalUnitKOneClass_inv]

/-- The original negative-chart rank-one calculation includes the zero ring. -/
private theorem zero_ring_negative_scalar_restrict_rankOne :
    perfectOpenKRestrict (laurentMinus (.of (ZMod 1))) 1
        (perfectScalarForwardKOneClass (laurentMinus (.of (ZMod 1)))
          (rankOnePerfect (Spec (.of (Polynomial (ZMod 1)))))
          (polynomialGlobalCoordinate (.of (ZMod 1))) (laurentGlobalUnit (.of (ZMod 1)))⁻¹
          (polynomialGlobalCoordinate_laurentMinus (.of (ZMod 1)))) =
      (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
        (rankOnePerfect (Spec (.of (LaurentPolynomial (ZMod 1))))))⁻¹ :=
  negative_scalar_restrict_rankOne _

end QuillenTest.GlobalUnitKOneInversion
