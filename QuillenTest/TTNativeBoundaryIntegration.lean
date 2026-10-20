/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import QuillenTest.AdditivityEndpointTransformationSquare
public import QuillenTest.AdditivityMixedTransformationSquare
public import QuillenTest.CoefficientBassPositiveSupportComposition
public import QuillenTest.CoefficientBassPositiveSupportMap
public import QuillenTest.CoefficientBassPositiveTransitionNaturality
public import QuillenTest.CommonReferenceNerveCompactFamily
public import QuillenTest.CommonReferenceNerveCompactStage
public import QuillenTest.DoubleCylinderSquare
public import QuillenTest.GodementTensorUnit
public import QuillenTest.IdentitySequence
public import QuillenTest.MWholeNerveCompositionReferences
public import QuillenTest.NativeCoefficientSelfTrackKZero
public import QuillenTest.NerveSquare
public import QuillenTest.ScalarCofiberSequenceMap
public import QuillenTest.ScalarSelfTrackBoundaryKZero
public import QuillenTest.ScalarUnitTrack
public import QuillenTest.ScalarUnitTrackNull
public import QuillenTest.ScalarUnitTrackOperation
public import QuillenTest.ScalarUnitTrackTransport
public import QuillenTest.SelfTrackIntertwining
public import QuillenTest.SelfTrackKOperationIntertwining
public import QuillenTest.SmallModelHomExt
public import QuillenTest.TTScalarConeIntegration
public import QuillenTest.WeakGridSquare
public import QuillenTest.WeakGridSquareRealization

/-! # Joint native boundary and original higher-coherence prerequisites -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProjectiveLine Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Products
  AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.TTNativeBoundaryIntegration
open FlasqueTwoSummands

local instance (R : CommRingCat.{u}) :
    CompactSpace (affineNativeChart R false ⁻¹ᵁ positiveOpen R).toScheme :=
  overlapOpen_compactSpace R

/-- The perfect K-groups carry the commutative group structure used by these tests. -/
local instance perfectKCommGroup (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
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

end QuillenTest.TTNativeBoundaryIntegration
