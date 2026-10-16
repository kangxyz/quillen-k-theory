/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoefficientConeFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitSelfTrackKZero
public import Quillen.Waldhausen.GrothendieckComparison.SmallModelHomExt

/-! # The original native coefficient boundary on every K-zero class

The actual forward Laurent unit operation after negative-chart restriction has
boundary the inverse of the literal native supported coefficient-cone K-map.
Original overlap transport, supported excision and support forgetting are retained.
The original small-model object-generator theorem extends the proved object formula.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open FlasqueTwoSummands


attribute [local instance] Waldhausen.Additivity.KCommGroup


/-- The original supported lower boundary equals the inverse native cone K-map on all K-zero. -/
theorem nativeLowerBoundary_comp_selfTrack_coefficient (R : CommRingCat.{u}) :
    (PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
        (affineNativeChart_cover R) 0).comp
      ((laurentOverlapEquiv R 1).symm.toMonoidHom.comp
        ((originalKSelfTrackOperation
          (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0).comp
            (perfectKRestrict (minusChart R) 0))) =
      invMonoidHom.comp (nativeTautologicalCoefficientConeKMap R 0) := by
  apply AlgebraicGrothendieck.kZero_hom_ext_ofSmallModel (perfectWaldhausen (twoChartLine R))
  intro K
  change PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
    (affineNativeChart_cover R) 0 ((laurentOverlapEquiv R 1).symm
      (originalKSelfTrackOperation _ _
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0
          (perfectKRestrict (minusChart R) 0
            ((perfectWaldhausen (twoChartLine R)).kZeroObjectClass K)))) =
    (nativeTautologicalCoefficientConeKMap R 0
      ((perfectWaldhausen (twoChartLine R)).kZeroObjectClass K))⁻¹
  have hr := KMap_kZeroObjectClass (perfectRestrict_waldhausenExact (minusChart R)) K
  change perfectKRestrict (minusChart R) 0
    ((perfectWaldhausen (twoChartLine R)).kZeroObjectClass K) = _ at hr
  rw [hr, perfectFlatUnitHomotopy_object, nativeTautologicalCoefficientConeKMap_objectClass]
  rw [← perfectGlobalUnitKOneClass_iso _ (laurentGlobalUnit R)
    ((perfectRestrictIsoFlatPullback (laurentMinus R)).app
      ((perfectRestrict (minusChart R)).obj K))]
  exact nativeLowerBoundary_forward_coefficient R K

/-- Original support forgetting gives the complete projective boundary homomorphism equation. -/
theorem laurentProjectiveConnecting_comp_selfTrack_coefficient (R : CommRingCat.{u}) :
    (laurentProjectiveConnecting R 0).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0).comp
          (perfectKRestrict (minusChart R) 0)) =
      invMonoidHom.comp ((perfectSupportedKMap (positiveOpen R).ι 0).comp
        (nativeTautologicalCoefficientConeKMap R 0)) := by
  apply MonoidHom.ext
  intro a
  have h := DFunLike.congr_fun (nativeLowerBoundary_comp_selfTrack_coefficient R) a
  exact (congrArg (perfectSupportedKMap (positiveOpen R).ι 0) h).trans
    (map_inv (perfectSupportedKMap (positiveOpen R).ι 0) _)

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
