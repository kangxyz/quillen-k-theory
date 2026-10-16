/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientCoordinate
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapCoefficientBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoordinateCone

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.Complex.LocalHomotopy
/-!
# The actual native supported cone with arbitrary perfect coefficients

The original left-tensor coordinate cone is transported by nativeAffineIso.inv. Its positive
support uses the actual positiveOpenIso and both composition comparisons. Its exact negative
supported restriction is the scalar cone on the literal minusChart restriction of the same
coefficient. Original supported excision and support forgetting give the unchanged projective
boundary with inverse sign. This is an object-class formula; no K-zero operation is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open FlasqueTwoSummands

/-- The original overlap compactness instance, at the literal inverse-image expression. -/
local instance nativeCoefficientOverlap_compactSpace (R : CommRingCat.{u}) :
    CompactSpace (affineNativeChart R false ⁻¹ᵁ positiveOpen R).toScheme :=
  overlapOpen_compactSpace R

/-- The original positive comparison on actual complexes, including both composition isos. -/
def nativeTautologicalCoefficientPositiveIso (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (restrict (positiveOpen R).ι).obj
        ((restrict (nativeAffineIso R).inv).obj (tautologicalCoefficientSupportedCone R K).obj) ≅
      (restrict (positiveOpenIso R).inv).obj
        ((restrict (plusChart R)).obj (tautologicalCoefficientSupportedCone R K).obj) :=
  ((restrictCompIso (positiveOpen R).ι (nativeAffineIso R).inv ≪≫
    eqToIso (restrict_congr (positiveOpen_inclusion_inverseAffine R)) ≪≫
      (restrictCompIso (positiveOpenIso R).inv (plusChart R)).symm).app _)

/-- The literal inverse-affine restriction of the original signed cone, with actual support. -/
def nativeTautologicalCoefficientSupportedCone (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (perfectSupported (positiveOpen R).ι).FullSubcategory :=
  ⟨(restrict (nativeAffineIso R).inv).obj (tautologicalCoefficientSupportedCone R K).obj,
    locallyPerfect_restrict _ (tautologicalCoefficientSupportedCone R K).property.1,
    fun n => (acyclic_restrict (positiveOpenIso R).inv
      (tautologicalCoefficientSupportedCone R K).property.2 n).of_iso
        (nativeTautologicalCoefficientPositiveIso R K).symm⟩

/-- Actual negative restriction is the scalar cone on the same restricted coefficient. -/
def nativeTautologicalCoefficientConeMinusIso (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (restrict (affineNativeChart R false)).obj
        (nativeTautologicalCoefficientSupportedCone R K).obj ≅
      CochainComplex.mappingCone
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app
          ((perfectRestrict (minusChart R)).obj K).obj) :=
  (restrictCompIso (affineNativeChart R false) (nativeAffineIso R).inv).app _ ≪≫
    (eqToIso (restrict_congr (affineNativeChart_false_inverseAffine R))).app _ ≪≫
      tautologicalCoefficientConeMinusIso R K

/-- The comparison is in the original supported category on the actual overlap open. -/
def nativeTautologicalCoefficientSupportedConeMinusIso (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (perfectSupportedRestrict (affineNativeChart R false) (positiveOpen R)).obj
        (nativeTautologicalCoefficientSupportedCone R K) ≅
      (perfectAcyclicToSupported (overlapOpen R).ι).obj
        (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
          (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
          ((perfectRestrict (minusChart R)).obj K)) :=
  (perfectSupported (overlapOpen R).ι).isoMk
    (nativeTautologicalCoefficientConeMinusIso R K)

/-- Actual supported restriction sends the native cone class to that exact local scalar class. -/
theorem nativeTautologicalCoefficientSupportedCone_restrict_class (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    perfectSupportedKRestrict (affineNativeChart R false) (positiveOpen R) 0
        ((perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
          (nativeTautologicalCoefficientSupportedCone R K)) =
      (perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen R).ι).obj
          (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
            (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
            ((perfectRestrict (minusChart R)).obj K))) :=
  (KMap_kZeroObjectClass (perfectSupportedRestrict_exact
    (affineNativeChart R false) (positiveOpen R)) _).trans
      ((perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass_iso
        (nativeTautologicalCoefficientSupportedConeMinusIso R K))

/-- The original excision inverse is determined by the actual supported restriction, not a
chosen preimage. -/
theorem nativeTautologicalCoefficientSupportedCone_excision (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
      (affineNativeChart_cover R) 0).symm
        ((perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
          ((perfectAcyclicToSupported (overlapOpen R).ι).obj
            (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
              (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
              ((perfectRestrict (minusChart R)).obj K)))) =
      (perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoefficientSupportedCone R K) := by
  apply (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
    (affineNativeChart_cover R) 0).injective
  rw [MulEquiv.apply_symm_apply]
  exact (nativeTautologicalCoefficientSupportedCone_restrict_class R K).symm

/-- The original lower boundary of the actual Laurent coefficient is the inverse supported cone. -/
theorem nativeLowerBoundary_forward_coefficient (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
        (affineNativeChart_cover R) 0
        ((laurentOverlapEquiv R 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
            ((perfectRestrict (laurentMinus R)).obj
            ((perfectRestrict (minusChart R)).obj K)))) =
      ((perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoefficientSupportedCone R K))⁻¹ := by
  change (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
    (affineNativeChart_cover R) 0).symm
      (qcqsPerfectConnectingHom (overlapOpen R).ι 0 _) = _
  rw [laurentOverlap_forward_coefficient_boundary, map_inv,
    nativeTautologicalCoefficientSupportedCone_excision]

/-- The original projective Mayer--Vietoris boundary, with its unchanged overlap transport and
support forgetting, is the inverse actual native coefficient cone class. -/
theorem laurentProjectiveConnecting_forward_coefficient (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    laurentProjectiveConnecting R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          ((perfectRestrict (laurentMinus R)).obj
            ((perfectRestrict (minusChart R)).obj K))) =
      ((perfectWaldhausen (nativeLineFunctor.obj (affineBase R)).obj).kZeroObjectClass
        ⟨(nativeTautologicalCoefficientSupportedCone R K).obj,
          (nativeTautologicalCoefficientSupportedCone R K).property.1⟩)⁻¹ := by
  exact (congrArg (perfectSupportedKMap (positiveOpen R).ι 0)
    (nativeLowerBoundary_forward_coefficient R K)).trans
      ((map_inv (perfectSupportedKMap (positiveOpen R).ι 0) _).trans
        (congrArg Inv.inv (KMap_kZeroObjectClass
          (subcategoryInclusion_exact (perfectSupported (positiveOpen R).ι)
            (locallyPerfect _) (fun _ h => h.1)) _)))

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
