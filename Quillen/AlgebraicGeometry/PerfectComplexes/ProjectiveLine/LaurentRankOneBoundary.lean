/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentRankOnePhiBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassPositiveFundamental

/-!
# The rank-one sign of the original Laurent Bass boundary

The original forward Laurent unit has projective boundary the inverse signed coordinate cone.
Its coefficients under the unchanged native Phi inverse are therefore (e⁻¹,e), where e denotes
the original rank-one K-zero object class; it is not replaced by the group identity. The Bass map
is the original first-coordinate projection. This object-level rank-one calculation does not
assert the all-object operation, additivity, or the all-degree Bass splitting.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open FlasqueTwoSummands

/-- The same native Phi inverse used by the original Bass row gives (inverse rank one, rank one).
-/
theorem connectingCoefficients_forward_rankOne (R : CommRingCat.{u}) :
    connectingCoefficients R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      (((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹,
        (perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R))) := by
  change (nativeGlobalTwoSummandKEquiv (affineBase R) 0).symm
    (laurentProjectiveConnecting R 0 _) = _
  rw [laurentProjectiveConnecting_forward_rankOne_Phi]
  exact (nativeGlobalTwoSummandKEquiv (affineBase R) 0).symm_apply_apply _

/-- The literal forward T has inverse rank-one terminal value for the original T-first row. -/
theorem positiveBassBoundary_forward_rankOne (R : CommRingCat.{u}) :
    positiveBassBoundary R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹ :=
  congrArg Prod.fst (connectingCoefficients_forward_rankOne R)

/-- The terminal sign also applies to the original normalized forward polynomial scalar square,
through its original open restriction K-map and canonical rebase. -/
theorem positiveBassBoundary_polynomialScalarForward_rankOne (R : CommRingCat.{u}) :
    positiveBassBoundary R 0
        (perfectOpenKRestrict (laurentPlus R) 1
          (perfectScalarForwardKOneClass (laurentPlus R)
            (rankOnePerfect (Spec (.of (Polynomial R)))) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R))) =
      ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹ := by
  rw [polynomialScalarForwardKOneClass_restrict_rankOne,
    positiveBassBoundary_forward_rankOne]

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
