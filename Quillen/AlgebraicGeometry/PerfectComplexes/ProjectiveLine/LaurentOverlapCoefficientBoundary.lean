/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapScalarBoundary

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
/-!
# The original overlap boundary with actual restricted coefficients

The coefficient on the Laurent chart is the literal negative Laurent restriction of a perfect
complex on the polynomial chart. The original inverse overlap map, its geometric composition
comparison and the original inverse-scalar boundary retain that coefficient without choosing a
preimage. This is an object-class boundary identity, not an operation on K-zero or all degrees.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The actual nested restriction is the original overlap restriction of the same coefficient. -/
def laurentOverlapCoefficientIso (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (perfectRestrict (overlapOpenIso R).inv).obj ((perfectRestrict (laurentMinus R)).obj K) ≅
      (perfectRestrict (overlapOpen R).ι).obj K :=
  (locallyPerfect (overlapOpen R).toScheme).isoMk
    ((restrictCompIso (overlapOpenIso R).inv (laurentMinus R)).app K.obj ≪≫
      (eqToIso (restrict_congr (overlapOpenIso_inv_laurentMinus R))).app K.obj)

/-- Original overlap transport preserves the unit on the actual restricted coefficient. -/
theorem laurentOverlapEquiv_symm_globalUnit_coefficient (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (laurentOverlapEquiv R 1).symm
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          ((perfectRestrict (laurentMinus R)).obj K)) =
      perfectGlobalUnitKOneClass _ (overlapLaurentGlobalUnit R)
        ((perfectRestrict (overlapOpen R).ι).obj K) := by
  change perfectKRestrict (overlapOpenIso R).inv 1 _ = _
  rw [perfectGlobalUnitKOneClass_restrict]
  exact perfectGlobalUnitKOneClass_iso _ _ (laurentOverlapCoefficientIso R K)

/-- The actual forward Laurent unit boundary is inverse of the same supported scalar cone. -/
theorem laurentOverlap_forward_coefficient_boundary (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    qcqsPerfectConnectingHom (overlapOpen R).ι 0
        ((laurentOverlapEquiv R 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
            ((perfectRestrict (laurentMinus R)).obj K))) =
      ((perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen R).ι).obj
          (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
            (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R) K)))⁻¹ := by
  rw [laurentOverlapEquiv_symm_globalUnit_coefficient]
  exact qcqsPerfectConnectingHom_globalUnit_inverse_scalar (overlapOpen R).ι K
    (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)
    (polynomialGlobalCoordinate_overlap R)

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
