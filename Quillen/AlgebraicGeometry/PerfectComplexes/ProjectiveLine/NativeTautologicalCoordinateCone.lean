/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoordinateCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapScalarBoundary

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.Complex.LocalHomotopy
/-!
# The original native supported coordinate cone and actual excision

The two-chart coordinate cone is transported by the inverse of the original native affine
isomorphism. Its support is the complement of the actual positive open, and its actual negative
supported restriction is the same scalar cone used by the original overlap boundary. Cancelling
the original supported excision equivalence identifies the original projective boundary. The
native Phi coordinates, and hence the terminal Bass sign, are separate computations.
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
local instance nativeCoordinateOverlap_compactSpace (R : CommRingCat.{u}) :
    CompactSpace (affineNativeChart R false ⁻¹ᵁ positiveOpen R).toScheme :=
  overlapOpen_compactSpace R

/-- The actual negative chart followed by inverse affine comparison is the original chart. -/
theorem affineNativeChart_false_inverseAffine (R : CommRingCat.{u}) :
    affineNativeChart R false ≫ (nativeAffineIso R).inv = minusChart R := by
  rw [affineNativeChart_false, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The positive open comparison retains the actual inverse native affine transport. -/
theorem positiveOpen_inclusion_inverseAffine (R : CommRingCat.{u}) :
    (positiveOpen R).ι ≫ (nativeAffineIso R).inv =
      (positiveOpenIso R).inv ≫ plusChart R := by
  apply (cancel_epi (positiveOpenIso R).hom).mp
  rw [← Category.assoc, positiveOpenIso_hom_inclusion, affineNativeChart_true,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- The original positive comparison on actual complexes, including both composition isos. -/
def nativeTautologicalCoordinatePositiveIso (R : CommRingCat.{u}) :
    (restrict (positiveOpen R).ι).obj
        ((restrict (nativeAffineIso R).inv).obj (tautologicalCoordinateSupportedCone R).obj) ≅
      (restrict (positiveOpenIso R).inv).obj
        ((restrict (plusChart R)).obj (tautologicalCoordinateSupportedCone R).obj) :=
  ((restrictCompIso (positiveOpen R).ι (nativeAffineIso R).inv ≪≫
    eqToIso (restrict_congr (positiveOpen_inclusion_inverseAffine R)) ≪≫
      (restrictCompIso (positiveOpenIso R).inv (plusChart R)).symm).app _)

/-- The literal inverse-affine restriction of the original signed cone, with actual support. -/
def nativeTautologicalCoordinateSupportedCone (R : CommRingCat.{u}) :
    (perfectSupported (positiveOpen R).ι).FullSubcategory :=
  ⟨(restrict (nativeAffineIso R).inv).obj (tautologicalCoordinateSupportedCone R).obj,
    locallyPerfect_restrict _ (tautologicalCoordinateSupportedCone R).property.1,
    fun n => (acyclic_restrict (positiveOpenIso R).inv
      (tautologicalCoordinateSupportedCone R).property.2 n).of_iso
        (nativeTautologicalCoordinatePositiveIso R).symm⟩

/-- Negative restriction of the actual native cone is the original rank-one polynomial cone. -/
def nativeTautologicalCoordinateConeMinusIso (R : CommRingCat.{u}) :
    (restrict (affineNativeChart R false)).obj
        (nativeTautologicalCoordinateSupportedCone R).obj ≅
      CochainComplex.mappingCone
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app
          (rankOnePerfect (Spec (.of (Polynomial R)))).obj) :=
  (restrictCompIso (affineNativeChart R false) (nativeAffineIso R).inv).app _ ≪≫
    (eqToIso (restrict_congr (affineNativeChart_false_inverseAffine R))).app _ ≪≫
      tautologicalCoordinateConeMinusGlobalScalarIso R

/-- The comparison is in the original supported category on the actual overlap open. -/
def nativeTautologicalCoordinateSupportedConeMinusIso (R : CommRingCat.{u}) :
    (perfectSupportedRestrict (affineNativeChart R false) (positiveOpen R)).obj
        (nativeTautologicalCoordinateSupportedCone R) ≅
      (perfectAcyclicToSupported (overlapOpen R).ι).obj
        (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
          (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
          (rankOnePerfect (Spec (.of (Polynomial R))))) :=
  (perfectSupported (overlapOpen R).ι).isoMk
    (nativeTautologicalCoordinateConeMinusIso R)

/-- Actual supported restriction sends the native cone class to that exact local scalar class. -/
theorem nativeTautologicalCoordinateSupportedCone_restrict_class (R : CommRingCat.{u}) :
    perfectSupportedKRestrict (affineNativeChart R false) (positiveOpen R) 0
        ((perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
          (nativeTautologicalCoordinateSupportedCone R)) =
      (perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen R).ι).obj
          (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
            (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
            (rankOnePerfect (Spec (.of (Polynomial R)))))) :=
  (KMap_kZeroObjectClass (perfectSupportedRestrict_exact
    (affineNativeChart R false) (positiveOpen R)) _).trans
      ((perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass_iso
        (nativeTautologicalCoordinateSupportedConeMinusIso R))

/-- The original excision inverse is determined by the actual supported restriction, not a
chosen preimage. -/
theorem nativeTautologicalCoordinateSupportedCone_excision (R : CommRingCat.{u}) :
    (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
      (affineNativeChart_cover R) 0).symm
        ((perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
          ((perfectAcyclicToSupported (overlapOpen R).ι).obj
            (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
              (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
              (rankOnePerfect (Spec (.of (Polynomial R))))))) =
      (perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoordinateSupportedCone R) := by
  apply (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
    (affineNativeChart_cover R) 0).injective
  rw [MulEquiv.apply_symm_apply]
  exact (nativeTautologicalCoordinateSupportedCone_restrict_class R).symm

/-- The original native lower boundary of forward Laurent rank one is the inverse actual
supported coordinate cone. -/
theorem nativeLowerBoundary_forward_rankOne (R : CommRingCat.{u}) :
    PerfectMayerVietoris.lowerBoundary (affineNativeChart R false) (positiveOpen R)
        (affineNativeChart_cover R) 0
        ((laurentOverlapEquiv R 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
            (rankOnePerfect (Spec (.of (LaurentPolynomial R)))))) =
      ((perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoordinateSupportedCone R))⁻¹ := by
  change (perfectSupportedExcisionKEquiv (affineNativeChart R false) (positiveOpen R)
    (affineNativeChart_cover R) 0).symm
      (qcqsPerfectConnectingHom (overlapOpen R).ι 0 _) = _
  rw [laurentOverlap_forward_rankOne_boundary, map_inv,
    nativeTautologicalCoordinateSupportedCone_excision]

/-- The original projective Mayer--Vietoris boundary, with its unchanged overlap transport and
support forgetting, is the inverse actual native coordinate cone class. -/
theorem laurentProjectiveConnecting_forward_rankOne (R : CommRingCat.{u}) :
    laurentProjectiveConnecting R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      ((perfectWaldhausen (nativeLineFunctor.obj (affineBase R)).obj).kZeroObjectClass
        ⟨(nativeTautologicalCoordinateSupportedCone R).obj,
          (nativeTautologicalCoordinateSupportedCone R).property.1⟩)⁻¹ := by
  exact (congrArg (perfectSupportedKMap (positiveOpen R).ι 0)
    (nativeLowerBoundary_forward_rankOne R)).trans
      ((map_inv (perfectSupportedKMap (positiveOpen R).ι 0) _).trans
        (congrArg Inv.inv (KMap_kZeroObjectClass
          (subcategoryInclusion_exact (perfectSupported (positiveOpen R).ι)
            (locallyPerfect _) (fun _ h => h.1)) _)))

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
