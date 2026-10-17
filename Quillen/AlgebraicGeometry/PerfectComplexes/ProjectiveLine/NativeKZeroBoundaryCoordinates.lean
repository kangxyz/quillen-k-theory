/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientObjectBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitSelfTrackKZero
public import Quillen.Waldhausen.GrothendieckComparison.SmallModelHomExt
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitKOperation

/-!
# Original global K-zero unit-boundary coordinates

The unchanged global-unit self-track and the unchanged projective connecting map give the
inverse-first-coordinate Phi pair on every original K-zero class. Object-generator
extensionality is transported through the actual small-model K-equivalence. No inverse for
Phi is assumed or used.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine

variable (X : QuasiCompactSchemes.{u})

/-- The actual nested negative-chart coefficient is the actual flat Laurent coefficient. -/
def laurentFirstSummandIso (K : Perfect X.obj) :
    (perfectRestrict (Relative.minus.app X).hom).obj
        ((perfectRestrict (nativeMinus.app X).hom).obj
          ((nativeFirstSummand X).obj K)) ≅
      (perfectFlatPullback (Relative.minus.app X).hom).obj
        ((perfectFlatPullback (Relative.polynomialProjection.app X).hom).obj K) :=
  (perfectRestrict (Relative.minus.app X).hom).mapIso
      ((nativeFirstSummandChartIso X false).app K) ≪≫
    (perfectRestrictIsoFlatPullback (Relative.minus.app X).hom).app _

attribute [local instance] Waldhausen.Additivity.KCommGroup

variable [QuasiSeparatedSpace X.obj]

/-- The original forward Laurent unit operation has its actual global Phi coordinates in K-zero.
-/
theorem projectiveConnecting_comp_selfTrack_polynomial :
    (projectiveConnecting X 0).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Relative.polynomialFunctor.obj X).obj)
        (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)) 0).comp
          (perfectKFlatPullback (Relative.polynomialProjection.app X).hom 0)) =
      (nativeTwoSummandKMap X 0).comp
        (invMonoidHom.prod (MonoidHom.id (PerfectK X.obj 0))) := by
  apply AlgebraicGrothendieck.kZero_hom_ext_ofSmallModel (perfectWaldhausen X.obj)
  intro K
  change projectiveConnecting X 0
    (originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)) 0
        (perfectKFlatPullback (Relative.polynomialProjection.app X).hom 0
          ((perfectWaldhausen X.obj).kZeroObjectClass K))) =
    nativeTwoSummandKMap X 0
      (((perfectWaldhausen X.obj).kZeroObjectClass K)⁻¹,
        (perfectWaldhausen X.obj).kZeroObjectClass K)
  have hp := KMap_kZeroObjectClass
    (perfectFlatPullback_waldhausenExact (Relative.polynomialProjection.app X).hom) K
  change perfectKFlatPullback (Relative.polynomialProjection.app X).hom 0
    ((perfectWaldhausen X.obj).kZeroObjectClass K) = _ at hp
  rw [hp, perfectFlatUnitHomotopy_object]
  rw [← perfectGlobalUnitKOneClass_iso _ (laurentGlobalUnit X) (laurentFirstSummandIso X K)]
  exact projectiveConnecting_forward_coefficient_phi X K

/-- The actual inverse-unit operation has the original pair with the first coordinate unchanged.
-/
theorem projectiveConnecting_comp_inverseSelfTrack_polynomial :
    (projectiveConnecting X 0).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Relative.polynomialFunctor.obj X).obj)
        (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)⁻¹) 0).comp
          (perfectKFlatPullback (Relative.polynomialProjection.app X).hom 0)) =
      (nativeTwoSummandKMap X 0).comp
        ((MonoidHom.id (PerfectK X.obj 0)).prod invMonoidHom) := by
  apply MonoidHom.ext
  intro a
  have h := DFunLike.congr_fun (projectiveConnecting_comp_selfTrack_polynomial X) a
  change projectiveConnecting X 0
    (originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)⁻¹) 0
        (perfectKFlatPullback (Relative.polynomialProjection.app X).hom 0 a)) =
    nativeTwoSummandKMap X 0 (a, a⁻¹)
  rw [perfectFlatUnitHomotopy_originalKOperation_inv, map_inv]
  change projectiveConnecting X 0
    (originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)) 0
        (perfectKFlatPullback (Relative.polynomialProjection.app X).hom 0 a)) =
    nativeTwoSummandKMap X 0 (a⁻¹, a) at h
  rw [h, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
