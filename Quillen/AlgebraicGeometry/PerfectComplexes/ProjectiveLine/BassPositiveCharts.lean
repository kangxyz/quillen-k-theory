/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.ZeroSection
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalBundle
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullback

/-! # Actual affine chart and evaluation maps for the positive Bass row

The polynomial and Laurent vertices are literal spectra of the original
rings. Canonical native chart comparisons retain both original Laurent
legs. Actual polynomial evaluation retracts the coefficient map on the
original perfect K-groups, in every natural degree and over every base ring.
-/
@[expose] public section
open Quillen


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
export AlgebraicGeometry.Scheme.PolynomialLaurent
  (polynomialZeroSection polynomialZeroSection_projection)
end Quillen.PerfectComplexes.ProjectiveLine.BassPositive

end



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Bass
open FlasqueTwoSummands

variable (R : CommRingCat.{u})

/-- Literal polynomial spectra map to the actual native projective line by its chosen charts. -/
def affineNativeChart (b : Bool) : Spec (.of (Polynomial R)) ⟶
    (nativeLineFunctor.obj (affineBase R)).obj :=
  (polynomialSpecIso R).hom ≫ nativeChart (affineBase R) b

instance affineNativeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (affineNativeChart R b) := by
  unfold affineNativeChart
  infer_instance

lemma affineNativeChart_true : affineNativeChart R true =
    plusChart R ≫ (nativeAffineIso R).hom :=
  (nativeAffineIso_plus R).symm

lemma affineNativeChart_false : affineNativeChart R false =
    minusChart R ≫ (nativeAffineIso R).hom :=
  (nativeAffineIso_minus R).symm

/-- The original two-chart cartesian square, through the actual native affine isomorphism. -/
theorem affineNativeChart_isPullback :
    IsPullback (PolynomialLaurent.laurentPlus R) (PolynomialLaurent.laurentMinus R)
      (affineNativeChart R true) (affineNativeChart R false) := by
  apply (chart_isPullback R).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (nativeAffineIso R)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, affineNativeChart_true]
  · simp only [Iso.refl_hom, Category.id_comp, affineNativeChart_false]

/-- The first open is the range of the actual positive polynomial chart. -/
def positiveOpen : (nativeLineFunctor.obj (affineBase R)).obj.Opens :=
  (affineNativeChart R true).opensRange

/-- The actual overlap open inside the negative polynomial chart. -/
def overlapOpen : (Spec (.of (Polynomial R))).Opens :=
  affineNativeChart R false ⁻¹ᵁ positiveOpen R

theorem laurentMinus_opensRange : (PolynomialLaurent.laurentMinus R).opensRange =
    overlapOpen R := by
  let h := (affineNativeChart_isPullback R).flip
  have hh : (h.isoPullback.hom ≫ pullback.fst
      (affineNativeChart R false) (affineNativeChart R true)).opensRange =
      affineNativeChart R false ⁻¹ᵁ (affineNativeChart R true).opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  simpa only [h.isoPullback_hom_fst, overlapOpen, positiveOpen] using hh

/-- Canonical comparison of the literal positive polynomial spectrum with its range open. -/
def positiveOpenIso : Spec (.of (Polynomial R)) ≅ (positiveOpen R).toScheme :=
  IsOpenImmersion.isoOfRangeEq (affineNativeChart R true) (positiveOpen R).ι (by
    change ((affineNativeChart R true).opensRange :
      Set (nativeLineFunctor.obj (affineBase R)).obj) = _
    exact Subtype.range_coe.symm)

/-- Canonical comparison of the literal Laurent spectrum with the original overlap. -/
def overlapOpenIso : Spec (.of (LaurentPolynomial R)) ≅ (overlapOpen R).toScheme :=
  IsOpenImmersion.isoOfRangeEq (PolynomialLaurent.laurentMinus R) (overlapOpen R).ι (by
    change ((PolynomialLaurent.laurentMinus R).opensRange : Set (Spec (.of (Polynomial R)))) = _
    rw [laurentMinus_opensRange]
    exact Subtype.range_coe.symm)

@[reassoc (attr := simp)] lemma positiveOpenIso_hom_inclusion :
    (positiveOpenIso R).hom ≫ (positiveOpen R).ι = affineNativeChart R true :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)] lemma overlapOpenIso_hom_inclusion :
    (overlapOpenIso R).hom ≫ (overlapOpen R).ι = PolynomialLaurent.laurentMinus R :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The overlap comparison retains the original positive Laurent leg. -/
@[reassoc] lemma overlapOpenIso_hom_toPositive :
    (overlapOpenIso R).hom ≫
        (affineNativeChart R false).resLE (positiveOpen R) (overlapOpen R) le_rfl =
      PolynomialLaurent.laurentPlus R ≫ (positiveOpenIso R).hom := by
  apply (cancel_mono (positiveOpen R).ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    overlapOpenIso_hom_inclusion, Category.assoc, positiveOpenIso_hom_inclusion]
  exact (affineNativeChart_isPullback R).w.symm

instance positiveOpen_compactSpace : CompactSpace (positiveOpen R).toScheme :=
  (AlgebraicGeometry.Scheme.homeoOfIso (positiveOpenIso R)).compactSpace

instance overlapOpen_compactSpace : CompactSpace (overlapOpen R).toScheme :=
  (AlgebraicGeometry.Scheme.homeoOfIso (overlapOpenIso R)).compactSpace

theorem positiveOpen_isCompact :
    IsCompact (positiveOpen R : Set (nativeLineFunctor.obj (affineBase R)).obj) :=
  isCompact_range (affineNativeChart R true).continuous

/-- The original two charts cover the actual native affine projective line. -/
theorem affineNativeChart_cover (x : (nativeLineFunctor.obj (affineBase R)).obj) :
    x ∈ Set.range (affineNativeChart R false) ∨ x ∈ positiveOpen R := by
  rcases native_charts_cover (affineBase R) x with ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨z, hz⟩ := (AlgebraicGeometry.Scheme.homeoOfIso (polynomialSpecIso R)).surjective y
    right
    refine ⟨z, ?_⟩
    change (nativePlus.app (affineBase R)).hom ((polynomialSpecIso R).hom z) = x
    exact (congrArg (nativePlus.app (affineBase R)).hom hz).trans hy
  · obtain ⟨z, hz⟩ := (AlgebraicGeometry.Scheme.homeoOfIso (polynomialSpecIso R)).surjective y
    left
    refine ⟨z, ?_⟩
    change (nativeMinus.app (affineBase R)).hom ((polynomialSpecIso R).hom z) = x
    exact (congrArg (nativeMinus.app (affineBase R)).hom hz).trans hy

/-- The original coefficient map to the literal polynomial spectrum. -/
def polynomialCoefficientKMap (n : ℕ) :
    PerfectK (Spec R) n →* PerfectK (Spec (.of (Polynomial R))) n :=
  perfectKFlatPullback (PolynomialLaurent.polynomialProjection R) n

/-- The original arbitrary geometric perfect pullback along actual polynomial evaluation. -/
def polynomialEvaluationKMap (n : ℕ) :
    PerfectK (Spec (.of (Polynomial R))) n →* PerfectK (Spec R) n :=
  perfectKPullback (polynomialZeroSection R) n

/-- Polynomial coefficient extension has the actual zero-evaluation left inverse. -/
theorem polynomialEvaluationKMap_comp_coefficient (n : ℕ) :
    (polynomialEvaluationKMap R n).comp (polynomialCoefficientKMap R n) =
      MonoidHom.id (PerfectK (Spec R) n) := by
  dsimp only [polynomialEvaluationKMap, polynomialCoefficientKMap]
  rw [← perfectKPullback_eq_flatPullback (PolynomialLaurent.polynomialProjection R) n,
    ← perfectKPullback_comp]
  simp only [polynomialZeroSection_projection, perfectKPullback_id]

theorem polynomialCoefficientKMap_injective (n : ℕ) :
    Function.Injective (polynomialCoefficientKMap R n) := by
  have h : Function.LeftInverse (polynomialEvaluationKMap R n)
      (polynomialCoefficientKMap R n) :=
    fun x => DFunLike.congr_fun (polynomialEvaluationKMap_comp_coefficient R n) x
  exact h.injective

/-- The canonical affine chart comparison retains literal polynomial coefficient pullback. -/
theorem polynomialCoefficientKMap_transport (n : ℕ) :
    (perfectKRestrict (polynomialSpecIso R).hom n).comp
        (perfectKFlatPullback (polynomialProjection.app (affineBase R)).hom n) =
      polynomialCoefficientKMap R n := by
  have hgeom : (polynomialSpecIso R).hom ≫
      (polynomialProjection.app (affineBase R)).hom =
      PolynomialLaurent.polynomialProjection R := polynomialSpecIso_hom_fst R
  rw [← perfectKFlatPullback_eq_restrict (polynomialSpecIso R).hom n,
    ← perfectKFlatPullback_comp]
  simp only [hgeom, polynomialCoefficientKMap]

/-- Both actual native Phi summands become the same literal polynomial coefficient map. -/
theorem affineNativeChart_Phi (b : Bool) (n : ℕ) (a c : PerfectK (Spec R) n) :
    perfectKRestrict (affineNativeChart R b) n
        (nativeTwoSummandKMap (affineBase R) n (a, c)) =
      polynomialCoefficientKMap R n (a * c) := by
  have hcomp := perfectKRestrict_comp (polynomialSpecIso R).hom
    (nativeChart (affineBase R) b) n
  change perfectKRestrict ((polynomialSpecIso R).hom ≫ nativeChart (affineBase R) b) n
    (nativeTwoSummandKMap (affineBase R) n (a, c)) = _
  rw [hcomp, MonoidHom.comp_apply]
  calc
    _ = perfectKRestrict (polynomialSpecIso R).hom n
        (perfectKFlatPullback (polynomialProjection.app (affineBase R)).hom n a *
          perfectKFlatPullback (polynomialProjection.app (affineBase R)).hom n c) :=
      congrArg (perfectKRestrict (polynomialSpecIso R).hom n)
        (nativeTwoSummandKMap_chart (affineBase R) b n a c)
    _ = polynomialCoefficientKMap R n a * polynomialCoefficientKMap R n c := by
      rw [map_mul]
      exact congrArg₂ (· * ·)
        (DFunLike.congr_fun (polynomialCoefficientKMap_transport R n) a)
        (DFunLike.congr_fun (polynomialCoefficientKMap_transport R n) c)
    _ = polynomialCoefficientKMap R n (a * c) := (polynomialCoefficientKMap R n).map_mul a c |>.symm

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
