/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalCoefficientConeAdditivity
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalCoefficientSelfTrackBoundary

/-!
# Global native unit-boundary coordinates in every connective degree

The literal global coefficient cone has the original Phi difference on each first-summand
input. Actual negative restriction and the scalar self-track boundary give the forward unit
coordinates, and actual unit inversion gives the reverse coordinates. Phi is only used as
its original forward K-map; no inverse or bijectivity hypothesis is needed.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass

variable (X : QuasiCompactSchemes.{u})

/-- The actual tensor K-map is the original native negative-twist map. -/
theorem coefficientTensorKMap_eq_nativeNegativeTwist (n : ℕ) :
    coefficientTensorKMap X n = KMap (nativeNegativeTwist_exact X) n := rfl

/-- Original cone additivity on the original first summand has the literal Phi pair. -/
theorem coefficientConeKMap_forget_phi (n : ℕ) (a : PerfectK X.obj n) :
    perfectSupportedKMap (positiveOpen X).ι n
      (coefficientConeKMap X n (KMap (nativeFirstSummand_exact X) n a)) =
        nativeTwoSummandKMap X n (a, a⁻¹) := by
  rw [coefficientConeKMap_forget, coefficientTensorKMap_eq_nativeNegativeTwist,
    nativeTwoSummandKMap_apply, map_inv]
  congr 1
  exact congrArg Inv.inv (DFunLike.congr_fun
    (KMap_comp_KMap (nativeFirstSummand_exact X) (nativeNegativeTwist_exact X) n) a)

attribute [local instance] Waldhausen.Additivity.KCommGroup

variable [QuasiSeparatedSpace X.obj]

/-- The unchanged forward Laurent unit has its global original Phi coordinates in every degree. -/
theorem projectiveConnecting_comp_selfTrack_polynomial_allDegrees (n : ℕ) :
    (projectiveConnecting X n).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Relative.polynomialFunctor.obj X).obj)
        (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)) n).comp
          (perfectKFlatPullback (Relative.polynomialProjection.app X).hom n)) =
      (nativeTwoSummandKMap X n).comp
        (invMonoidHom.prod (MonoidHom.id (PerfectK X.obj n))) := by
  apply MonoidHom.ext
  intro a
  have hp := DFunLike.congr_fun (nativeFirstSummandKMap_chart X false n) a
  change perfectKRestrict (nativeMinus.app X).hom n
    (KMap (nativeFirstSummand_exact X) n a) =
      perfectKFlatPullback (Relative.polynomialProjection.app X).hom n a at hp
  change projectiveConnecting X n
    (originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)) n
        (perfectKFlatPullback (Relative.polynomialProjection.app X).hom n a)) =
    nativeTwoSummandKMap X n (a⁻¹, a)
  rw [← hp, projectiveConnecting_selfTrack_coefficient_allDegrees,
    coefficientConeKMap_forget_phi, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

/-- Actual inverse-unit operation gives the unchanged first coordinate in every degree. -/
theorem projectiveConnecting_comp_inverseSelfTrack_polynomial_allDegrees (n : ℕ) :
    (projectiveConnecting X n).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Relative.polynomialFunctor.obj X).obj)
        (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)⁻¹) n).comp
          (perfectKFlatPullback (Relative.polynomialProjection.app X).hom n)) =
      (nativeTwoSummandKMap X n).comp
        ((MonoidHom.id (PerfectK X.obj n)).prod invMonoidHom) := by
  apply MonoidHom.ext
  intro a
  have h := DFunLike.congr_fun
    (projectiveConnecting_comp_selfTrack_polynomial_allDegrees X n) a
  change projectiveConnecting X n
    (originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)⁻¹) n
        (perfectKFlatPullback (Relative.polynomialProjection.app X).hom n a)) =
    nativeTwoSummandKMap X n (a, a⁻¹)
  rw [perfectFlatUnitHomotopy_originalKOperation_inv, map_inv]
  change projectiveConnecting X n
    (originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)) n
        (perfectKFlatPullback (Relative.polynomialProjection.app X).hom n a)) =
    nativeTwoSummandKMap X n (a⁻¹, a) at h
  rw [h, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
