/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientSelfTrackBoundary

/-! # Strict clients of the original native coefficient boundary in all connective degrees -/
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
namespace QuillenTest.NativeCoefficientSelfTrackBoundary
open FlasqueTwoSummands

local instance (R : CommRingCat.{u}) :
    CompactSpace (affineNativeChart R false ⁻¹ᵁ positiveOpen R).toScheme :=
  overlapOpen_compactSpace R

/-- The perfect K-groups carry the commutative group structure used by these tests. -/
local instance perfectKCommGroup (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

/-- The supported K-groups carry the commutative group structure used by these tests. -/
local instance perfectSupportedKCommGroup {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    CommGroup (PerfectSupportedK j n) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectSupportedWaldhausen j) n

/-- The full supported homomorphism retains the actual inverse overlap and lower boundary. -/
theorem original_supported_homomorphism (R : CommRingCat.{u}) (n : ℕ) :
    (PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
        (affineNativeChart_cover R) n).comp
      ((laurentOverlapEquiv R (n + 1)).symm.toMonoidHom.comp
        ((originalKSelfTrackOperation
          (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n).comp
            (perfectKRestrict (minusChart R) n))) =
      invMonoidHom.comp (nativeTautologicalCoefficientConeKMap R n) :=
  nativeLowerBoundary_comp_selfTrack_coefficient_allDegrees R n

/-- The supported formula holds on every original projective-line input. -/
theorem arbitrary_original_supported_input (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (twoChartLine R) n) :
    PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
      (affineNativeChart_cover R) n ((laurentOverlapEquiv R (n + 1)).symm
        (originalKSelfTrackOperation
          (perfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
          (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
            (perfectKRestrict (minusChart R) n a))) =
      (nativeTautologicalCoefficientConeKMap R n a)⁻¹ :=
  nativeLowerBoundary_selfTrack_coefficient_allDegrees R n a

/-- Support forgetting gives the original projective boundary on the full homomorphism. -/
theorem original_projective_homomorphism (R : CommRingCat.{u}) (n : ℕ) :
    (laurentProjectiveConnecting R n).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n).comp
          (perfectKRestrict (minusChart R) n)) =
      invMonoidHom.comp ((perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n)) :=
  laurentProjectiveConnecting_comp_selfTrack_coefficient_allDegrees R n

/-- Arbitrary coefficients retain the old projective map rather than a replacement section. -/
theorem arbitrary_original_projective_input (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (twoChartLine R) n) :
    laurentProjectiveConnecting R n
      (originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
          (perfectKRestrict (minusChart R) n a)) =
      (perfectSupportedKMap (positiveOpen R).ι n
        (nativeTautologicalCoefficientConeKMap R n a))⁻¹ :=
  laurentProjectiveConnecting_selfTrack_coefficient_allDegrees R n a

/-- Degree zero uses the same entire operation and no object representative is supplied. -/
theorem arbitrary_original_kzero (R : CommRingCat.{u}) (a : PerfectK (twoChartLine R) 0) :
    laurentProjectiveConnecting R 0
      (originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0
          (perfectKRestrict (minusChart R) 0 a)) =
      (perfectSupportedKMap (positiveOpen R).ι 0
        (nativeTautologicalCoefficientConeKMap R 0 a))⁻¹ :=
  laurentProjectiveConnecting_selfTrack_coefficient_allDegrees R 0 a

end QuillenTest.NativeCoefficientSelfTrackBoundary
