/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassPositiveCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.RestrictionIsoEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris
public import Mathlib.Algebra.Exact.Basic

/-! # Original projective-line Mayer-Vietoris on literal affine vertices

Canonical chart and overlap isomorphisms transport the original positive
sequence to literal polynomial and Laurent spectra. The positive chart is
the first factor, and the overlap map retains positive restriction times
the inverse of negative restriction. The boundary is the original boundary.
-/
@[expose] public section

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine FlasqueTwoSummands

/-- The commutative group structure on `PerfectK Y n` supplied by Waldhausen additivity. -/
local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

variable (R : CommRingCat.{u})

/-- The actual two native affine chart restrictions, in positive-negative order. -/
def affineRestrictionPair (n : ℕ) : PerfectK (nativeLineFunctor.obj (affineBase R)).obj n →*
    PerfectK (Spec (.of (Polynomial R))) n × PerfectK (Spec (.of (Polynomial R))) n :=
  (perfectKRestrict (affineNativeChart R true) n).prod
    (perfectKRestrict (affineNativeChart R false) n)

/-- Literal original positive Laurent restriction times inverse negative Laurent restriction. -/
def laurentDifference (n : ℕ) :
    PerfectK (Spec (.of (Polynomial R))) n × PerfectK (Spec (.of (Polynomial R))) n →*
      PerfectK (Spec (.of (LaurentPolynomial R))) n :=
  GroupMayerVietoris.difference (perfectKRestrict (PolynomialLaurent.laurentPlus R) n)
    (perfectKRestrict (PolynomialLaurent.laurentMinus R) n)

lemma laurentDifference_apply (n : ℕ)
    (a b : PerfectK (Spec (.of (Polynomial R))) n) :
    laurentDifference R n (a, b) =
      perfectKRestrict (PolynomialLaurent.laurentPlus R) n a *
        (perfectKRestrict (PolynomialLaurent.laurentMinus R) n b)⁻¹ := rfl

/-- Actual restriction identifies the first MV factor with the literal positive polynomial chart. -/
def positivePairEquiv (n : ℕ) :
    PerfectK (positiveOpen R).toScheme n × PerfectK (Spec (.of (Polynomial R))) n ≃*
      PerfectK (Spec (.of (Polynomial R))) n × PerfectK (Spec (.of (Polynomial R))) n :=
  MulEquiv.prodCongr (perfectKRestrictIsoEquiv (positiveOpenIso R) n) (MulEquiv.refl _)

/-- Actual restriction identifies the original overlap with the literal Laurent spectrum. -/
def laurentOverlapEquiv (n : ℕ) :
    PerfectK (overlapOpen R).toScheme n ≃* PerfectK (Spec (.of (LaurentPolynomial R))) n :=
  perfectKRestrictIsoEquiv (overlapOpenIso R) n

/-- The ORIGINAL projective-line MV boundary, through its actual Laurent overlap comparison. -/
def laurentProjectiveConnecting (n : ℕ) :
    PerfectK (Spec (.of (LaurentPolynomial R))) (n + 1) →*
      PerfectK (nativeLineFunctor.obj (affineBase R)).obj n :=
  (PerfectMayerVietoris.qcqsConnectingHom (affineNativeChart R false) (positiveOpen R)
    (positiveOpen_isCompact R) (affineNativeChart_cover R) n).comp
      (laurentOverlapEquiv R (n + 1)).symm.toMonoidHom

/-- The boundary has exactly the original geometric boundary and actual inverse restriction. -/
lemma laurentProjectiveConnecting_apply (n : ℕ)
    (x : PerfectK (Spec (.of (LaurentPolynomial R))) (n + 1)) :
    laurentProjectiveConnecting R n x =
      PerfectMayerVietoris.qcqsConnectingHom (affineNativeChart R false) (positiveOpen R)
        (positiveOpen_isCompact R) (affineNativeChart_cover R) n
          (perfectKRestrict (overlapOpenIso R).inv (n + 1) x) := rfl

theorem affineRestrictionPair_square (n : ℕ) :
    (positivePairEquiv R n).toMonoidHom.comp
        (PerfectMayerVietoris.restrictionPair (affineNativeChart R false) (positiveOpen R) n) =
      affineRestrictionPair R n := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · change perfectKRestrict (positiveOpenIso R).hom n
      (perfectKRestrict (positiveOpen R).ι n x) =
        perfectKRestrict (affineNativeChart R true) n x
    have h := perfectKRestrict_comp (positiveOpenIso R).hom (positiveOpen R).ι n
    simp only [positiveOpenIso_hom_inclusion] at h
    exact (DFunLike.congr_fun h x).symm
  · rfl

theorem laurentDifference_square (n : ℕ) :
    (laurentOverlapEquiv R n).toMonoidHom.comp
        (PerfectMayerVietoris.overlapDifference (affineNativeChart R false) (positiveOpen R) n) =
      (laurentDifference R n).comp (positivePairEquiv R n).toMonoidHom := by
  have hplus := perfectKRestrict_comp (overlapOpenIso R).hom
    ((affineNativeChart R false).resLE (positiveOpen R) (overlapOpen R) le_rfl) n
  simp only [overlapOpenIso_hom_toPositive] at hplus
  have hplus' := perfectKRestrict_comp (PolynomialLaurent.laurentPlus R)
    (positiveOpenIso R).hom n
  have hminus := perfectKRestrict_comp (overlapOpenIso R).hom (overlapOpen R).ι n
  simp only [overlapOpenIso_hom_inclusion] at hminus
  ext x
  change perfectKRestrict (overlapOpenIso R).hom n
      (perfectKRestrict
          ((affineNativeChart R false).resLE (positiveOpen R) (overlapOpen R) le_rfl) n x.1 *
        (perfectKRestrict (overlapOpen R).ι n x.2)⁻¹) =
    perfectKRestrict (PolynomialLaurent.laurentPlus R) n
      (perfectKRestrict (positiveOpenIso R).hom n x.1) *
        (perfectKRestrict (PolynomialLaurent.laurentMinus R) n x.2)⁻¹
  rw [map_mul, map_inv]
  exact congrArg₂ (fun a b => a * b⁻¹)
    (DFunLike.congr_fun (hplus.symm.trans hplus') x.1)
    (DFunLike.congr_fun hminus x.2).symm

theorem laurentProjectiveConnecting_square (n : ℕ) :
    (laurentProjectiveConnecting R n).comp (laurentOverlapEquiv R (n + 1)).toMonoidHom =
      PerfectMayerVietoris.qcqsConnectingHom (affineNativeChart R false) (positiveOpen R)
        (positiveOpen_isCompact R) (affineNativeChart_cover R) n := by
  ext x
  change PerfectMayerVietoris.qcqsConnectingHom (affineNativeChart R false) (positiveOpen R)
      (positiveOpen_isCompact R) (affineNativeChart_cover R) n
        ((laurentOverlapEquiv R (n + 1)).symm (laurentOverlapEquiv R (n + 1) x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- All original positive MV exact positions on literal polynomial and Laurent spectra. -/
theorem affine_positiveExactSequence (n : ℕ) :
    (affineRestrictionPair R (n + 1)).range = (laurentDifference R (n + 1)).ker ∧
    (laurentDifference R (n + 1)).range = (laurentProjectiveConnecting R n).ker ∧
    (laurentProjectiveConnecting R n).range = (affineRestrictionPair R n).ker := by
  let j := affineNativeChart R false
  let T := positiveOpen R
  let d := PerfectMayerVietoris.qcqsConnectingHom j T
    (positiveOpen_isCompact R) (affineNativeChart_cover R) n
  have h := PerfectMayerVietoris.qcqs_positiveExactSequence j T
    (positiveOpen_isCompact R) (affineNativeChart_cover R) n
  have hr : Function.MulExact (PerfectMayerVietoris.restrictionPair j T (n + 1))
      (PerfectMayerVietoris.overlapDifference j T (n + 1)) := MonoidHom.mulExact_iff.mpr h.1.symm
  have hd : Function.MulExact (PerfectMayerVietoris.overlapDifference j T (n + 1)) d :=
    MonoidHom.mulExact_iff.mpr h.2.1.symm
  have hs : Function.MulExact d (PerfectMayerVietoris.restrictionPair j T n) :=
    MonoidHom.mulExact_iff.mpr h.2.2.symm
  have hr' := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (PerfectMayerVietoris.restrictionPair j T (n + 1))
    (PerfectMayerVietoris.overlapDifference j T (n + 1))
    (affineRestrictionPair R (n + 1)) (laurentDifference R (n + 1))
    (MonoidHom.id _) (positivePairEquiv R (n + 1)).toMonoidHom
    (laurentOverlapEquiv R (n + 1)).toMonoidHom
    (by simpa only [MonoidHom.comp_id] using (affineRestrictionPair_square R (n + 1)).symm)
    (laurentDifference_square R (n + 1)).symm Function.surjective_id
    (positivePairEquiv R (n + 1)).bijective (laurentOverlapEquiv R (n + 1)).injective).mp hr
  have hd' := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (PerfectMayerVietoris.overlapDifference j T (n + 1)) d
    (laurentDifference R (n + 1)) (laurentProjectiveConnecting R n)
    (positivePairEquiv R (n + 1)).toMonoidHom (laurentOverlapEquiv R (n + 1)).toMonoidHom
    (MonoidHom.id _) (laurentDifference_square R (n + 1)).symm
    (by simpa only [MonoidHom.id_comp] using laurentProjectiveConnecting_square R n)
    (positivePairEquiv R (n + 1)).surjective (laurentOverlapEquiv R (n + 1)).bijective
    Function.injective_id).mp hd
  have hs' := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    d (PerfectMayerVietoris.restrictionPair j T n)
    (laurentProjectiveConnecting R n) (affineRestrictionPair R n)
    (laurentOverlapEquiv R (n + 1)).toMonoidHom (MonoidHom.id _)
    (positivePairEquiv R n).toMonoidHom
    (by simpa only [MonoidHom.id_comp] using laurentProjectiveConnecting_square R n)
    (by simpa only [MonoidHom.comp_id] using (affineRestrictionPair_square R n).symm)
    (laurentOverlapEquiv R (n + 1)).surjective Function.bijective_id
    (positivePairEquiv R n).injective).mp hs
  exact ⟨(MonoidHom.mulExact_iff.mp hr').symm, (MonoidHom.mulExact_iff.mp hd').symm,
    (MonoidHom.mulExact_iff.mp hs').symm⟩

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
