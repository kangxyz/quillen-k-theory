/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarConeKMapComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarSelfTrackGlobalBoundary
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapUnitOperation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoefficientConeFunctor

/-! # Original native coefficient boundaries in every connective degree

The actual inverse overlap restriction transports the original Laurent unit operation. The
polynomial scalar restricts to the inverse overlap unit, giving one inverse in the original
supported boundary. The literal cone-map comparison and original support excision retain the
native coefficient cone and support-forgetting maps on every original input class.
-/
@[expose] public section
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


/-- Actual overlap restriction and support excision give the inverse native cone on all inputs. -/
theorem nativeLowerBoundary_comp_selfTrack_coefficient_allDegrees
    (R : CommRingCat.{u}) (n : ℕ) :
    (PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
        (affineNativeChart_cover R) n).comp
      ((laurentOverlapEquiv R (n + 1)).symm.toMonoidHom.comp
        ((originalKSelfTrackOperation
          (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n).comp
            (perfectKRestrict (minusChart R) n))) =
      invMonoidHom.comp (nativeTautologicalCoefficientConeKMap R n) := by
  apply MonoidHom.ext
  intro a
  apply (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
    (affineNativeChart_cover R) n).injective
  change (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
    (affineNativeChart_cover R) n)
      ((perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
        (affineNativeChart_cover R) n).symm
          (qcqsPerfectConnectingHom (overlapOpen R).ι n
            ((laurentOverlapEquiv R (n + 1)).symm
              (originalKSelfTrackOperation _ _
                (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
                  (perfectKRestrict (minusChart R) n a))))) =
    (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
      (affineNativeChart_cover R) n) ((nativeTautologicalCoefficientConeKMap R n a)⁻¹)
  rw [MulEquiv.apply_symm_apply, map_inv]
  change qcqsPerfectConnectingHom (overlapOpen R).ι n
      ((laurentOverlapEquiv R (n + 1)).symm
        (originalKSelfTrackOperation _ _
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
            (perfectKRestrict (minusChart R) n a))) =
    (perfectSupportedKRestrict (affineNativeChart R false) (positiveOpen R) n
      (nativeTautologicalCoefficientConeKMap R n a))⁻¹
  rw [laurentOverlapEquiv_unitSelfTrack_inverse, map_inv,
    qcqsPerfectConnectingHom_scalarUnitSelfTrack (overlapOpen R).ι
      (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
      (polynomialGlobalCoordinate_overlap R),
    perfectAcyclicSupportedKEquiv_scalarConeKMap]
  exact congrArg Inv.inv
    (DFunLike.congr_fun (nativeTautologicalCoefficientConeKMap_restrict R n) a).symm

/-- Every original class retains the same negative chart, overlap transport and supported cone. -/
theorem nativeLowerBoundary_selfTrack_coefficient_allDegrees
    (R : CommRingCat.{u}) (n : ℕ) (a : PerfectK (twoChartLine R) n) :
    PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
      (affineNativeChart_cover R) n ((laurentOverlapEquiv R (n + 1)).symm
        (originalKSelfTrackOperation
          (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
            (perfectKRestrict (minusChart R) n a))) =
      (nativeTautologicalCoefficientConeKMap R n a)⁻¹ :=
  DFunLike.congr_fun (nativeLowerBoundary_comp_selfTrack_coefficient_allDegrees R n) a

/-- The original projective boundary is the support-forgotten inverse native coefficient cone. -/
theorem laurentProjectiveConnecting_comp_selfTrack_coefficient_allDegrees
    (R : CommRingCat.{u}) (n : ℕ) :
    (laurentProjectiveConnecting R n).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n).comp
          (perfectKRestrict (minusChart R) n)) =
      invMonoidHom.comp ((perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n)) := by
  apply MonoidHom.ext
  intro a
  have h := nativeLowerBoundary_selfTrack_coefficient_allDegrees R n a
  exact (congrArg (perfectSupportedKMap (positiveOpen R).ι n) h).trans
    (map_inv (perfectSupportedKMap (positiveOpen R).ι n) _)

/-- The all-degree projective formula uses arbitrary original inputs, including K-zero. -/
theorem laurentProjectiveConnecting_selfTrack_coefficient_allDegrees
    (R : CommRingCat.{u}) (n : ℕ) (a : PerfectK (twoChartLine R) n) :
    laurentProjectiveConnecting R n
      (originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
          (perfectKRestrict (minusChart R) n a)) =
      (perfectSupportedKMap (positiveOpen R).ι n
        (nativeTautologicalCoefficientConeKMap R n a))⁻¹ :=
  DFunLike.congr_fun (laurentProjectiveConnecting_comp_selfTrack_coefficient_allDegrees R n) a

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
