/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientSelfTrackKZero

/-! # The original native degree-zero boundary, as homomorphisms and on arbitrary classes -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProjectiveLine Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.NativeCoefficientSelfTrackKZero
open FlasqueTwoSummands

local instance (R : CommRingCat.{u}) :
    CompactSpace (affineNativeChart R false ⁻¹ᵁ positiveOpen R).toScheme :=
  overlapOpen_compactSpace R

local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

/-- The full original composite is the inverse of the actual support-forgotten cone K-map. -/
theorem original_homomorphism (R : CommRingCat.{u}) :
    (laurentProjectiveConnecting R 0).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0).comp
          (perfectKRestrict (minusChart R) 0)) =
      invMonoidHom.comp ((perfectSupportedKMap (positiveOpen R).ι 0).comp
        (nativeTautologicalCoefficientConeKMap R 0)) :=
  laurentProjectiveConnecting_comp_selfTrack_coefficient R

/-- No object representative is supplied for this arbitrary original K-zero input. -/
theorem arbitrary_original_kzero (R : CommRingCat.{u}) (a : PerfectK (twoChartLine R) 0) :
    laurentProjectiveConnecting R 0
      (originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0
          (perfectKRestrict (minusChart R) 0 a)) =
      (perfectSupportedKMap (positiveOpen R).ι 0
        (nativeTautologicalCoefficientConeKMap R 0 a))⁻¹ :=
  DFunLike.congr_fun (laurentProjectiveConnecting_comp_selfTrack_coefficient R) a

/-- The stronger original lower boundary retains its actual supported target. -/
theorem arbitrary_supported_boundary (R : CommRingCat.{u})
    (a : PerfectK (twoChartLine R) 0) :
    PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
      (affineNativeChart_cover R) 0 ((laurentOverlapEquiv R 1).symm
        (originalKSelfTrackOperation
          (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0
            (perfectKRestrict (minusChart R) 0 a))) =
      (nativeTautologicalCoefficientConeKMap R 0 a)⁻¹ :=
  DFunLike.congr_fun (nativeLowerBoundary_comp_selfTrack_coefficient R) a

end QuillenTest.NativeCoefficientSelfTrackKZero
