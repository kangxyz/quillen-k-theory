/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassPositiveMayerVietoris
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarSupportedBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneRestriction
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates

/-!
# The scalar boundary on the actual native-chart overlap

The inverse of the original Laurent-overlap equivalence is the actual geometric restriction
with its canonical zero rebase. It sends the original Laurent rank-one unit class to its
literal pulled-back unit on the overlap. The negative polynomial scalar restricts there to
the inverse unit, so its original localization boundary is the inverse supported scalar cone
class. Global supported excision and native Phi coordinates remain separate comparisons.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The actual Laurent unit pulled back along the original inverse overlap comparison. -/
def overlapLaurentGlobalUnit (R : CommRingCat.{u}) : (Γ((overlapOpen R).toScheme, ⊤))ˣ :=
  Units.map (overlapOpenIso R).inv.appTop.hom.toMonoidHom (laurentGlobalUnit R)

/-- The inverse original overlap comparison retains the original negative Laurent inclusion. -/
theorem overlapOpenIso_inv_laurentMinus (R : CommRingCat.{u}) :
    (overlapOpenIso R).inv ≫ laurentMinus R = (overlapOpen R).ι := by
  rw [← overlapOpenIso_hom_inclusion, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The unchanged negative polynomial scalar restricts to the inverse actual overlap unit. -/
theorem polynomialGlobalCoordinate_overlap (R : CommRingCat.{u}) :
    (overlapOpen R).ι.appTop (polynomialGlobalCoordinate R) =
      ↑((overlapLaurentGlobalUnit R)⁻¹) := by
  have h := congrArg (fun f => f.appTop) (overlapOpenIso_inv_laurentMinus R)
  rw [Scheme.Hom.comp_appTop] at h
  have hr := ConcreteCategory.congr_hom h (polynomialGlobalCoordinate R)
  change (overlapOpenIso R).inv.appTop
      ((laurentMinus R).appTop (polynomialGlobalCoordinate R)) =
    (overlapOpen R).ι.appTop (polynomialGlobalCoordinate R) at hr
  rw [polynomialGlobalCoordinate_laurentMinus] at hr
  exact hr.symm

/-- The inverse of the original overlap K-equivalence carries the actual forward rank-one unit. -/
theorem laurentOverlapEquiv_symm_globalUnit_rankOne (R : CommRingCat.{u}) :
    (laurentOverlapEquiv R 1).symm
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      perfectGlobalUnitKOneClass _ (overlapLaurentGlobalUnit R)
        (rankOnePerfect (overlapOpen R).toScheme) :=
  perfectGlobalUnitKOneClass_restrict_rankOne (overlapOpenIso R).inv (laurentGlobalUnit R)

/-- The original lower localization boundary of the original forward Laurent class is the
inverse of the actual supported scalar cone class on the negative chart. -/
theorem laurentOverlap_forward_rankOne_boundary (R : CommRingCat.{u}) :
    qcqsPerfectConnectingHom (overlapOpen R).ι 0
        ((laurentOverlapEquiv R 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
            (rankOnePerfect (Spec (.of (LaurentPolynomial R)))))) =
      ((perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen R).ι).obj
          (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
            (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
            (rankOnePerfect (Spec (.of (Polynomial R)))))))⁻¹ := by
  rw [laurentOverlapEquiv_symm_globalUnit_rankOne]
  have h := qcqsPerfectConnectingHom_globalUnit_rankOne (overlapOpen R).ι
    (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
    (polynomialGlobalCoordinate_overlap R)
  rw [perfectGlobalUnitKOneClass_inv, map_inv] at h
  simpa only [inv_inv] using congrArg Inv.inv h

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
