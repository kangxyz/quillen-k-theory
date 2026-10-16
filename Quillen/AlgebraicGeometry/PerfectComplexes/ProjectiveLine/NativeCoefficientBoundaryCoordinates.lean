/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientConeAdditivity
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientSelfTrackBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeAffineTwoSummands
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.RestrictionIsoEquivalence

/-! # Original native Phi coordinates of the coefficient boundary

The actual affine summand isomorphisms transport the original coefficient-cone difference to
Phi(a, a inverse). The original Laurent unit boundary is its inverse, hence Phi(a inverse, a).
All equations retain the original forward Phi map, every connective degree and arbitrary
coefficient classes, including degree zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open FlasqueTwoSummands

/-- Both Boolean chart trivializations are the original minus and plus line isomorphisms. -/
theorem coefficientTensor_lineChartIso (R : CommRingCat.{u}) (b : Bool) :
    lineChartIso R b = ((fun c => by
      cases c
      · exact tautologicalLineMinusIso R
      · exact tautologicalLinePlusIso R) :
        (c : Bool) → (tautologicalLine R).restrict (polynomialChart R c) ≅
          SheafOfModules.unit (Spec (CommRingCat.of (Polynomial R))).ringCatSheaf) b := by
  cases b <;> rfl

/-- The complete coefficient tensor functor is the actual original local negative twist. -/
theorem coefficientTensorFunctor_eq_localNegativeTwist (R : CommRingCat.{u}) :
    tautologicalCoefficientTensorFunctor R = localNegativeTwist R := by
  unfold tautologicalCoefficientTensorFunctor localNegativeTwist
  have hc : (fun b => by
      cases b
      · exact tautologicalLineMinusIso R
      · exact tautologicalLinePlusIso R) = lineChartIso R := by
    funext b
    exact (coefficientTensor_lineChartIso R b).symm
  rw [hc]

/-- The tensor K-map follows the actual whole-functor data identification. -/
theorem coefficientTensorKMap_eq_localNegativeTwist (R : CommRingCat.{u}) (n : ℕ) :
    tautologicalCoefficientTensorKMap R n = KMap (localNegativeTwist_exact R) n :=
  KMap_eq_of_iso (tautologicalCoefficientTensorFunctor_waldhausenExact R)
    (localNegativeTwist_exact R)
    (eqToIso (coefficientTensorFunctor_eq_localNegativeTwist R)) n

/-- Actual affine pullback transports the entire original first-summand homomorphism. -/
theorem nativeCoefficientFirst_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKFlatPullback (nativeAffineIso R).hom n).comp
        (KMap (nativeFirstSummand_exact (affineBase R)) n) =
      perfectKFlatPullback (projection R) n := by
  unfold perfectKFlatPullback
  rw [KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (nativeFirstTransportIso R) n

/-- Actual affine pullback transports the entire original second-summand homomorphism. -/
theorem nativeCoefficientSecond_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKFlatPullback (nativeAffineIso R).hom n).comp
        (KMap (nativeSecondSummand_exact (affineBase R)) n) =
      (tautologicalCoefficientTensorKMap R n).comp
        (perfectKFlatPullback (projection R) n) := by
  rw [coefficientTensorKMap_eq_localNegativeTwist]
  unfold perfectKFlatPullback
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (nativeSecondTransportIso R) n

/-- The original inverse-affine restriction cancels the original forward affine pullback. -/
theorem nativeCoefficientAffine_restrict_cancel (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (nativeAffineIso R).inv n).comp
        (perfectKFlatPullback (nativeAffineIso R).hom n) =
      MonoidHom.id (PerfectK (nativeLineFunctor.obj (affineBase R)).obj n) := by
  rw [perfectKFlatPullback_eq_restrict, ← perfectKRestrict_comp]
  simp only [Iso.inv_hom_id, perfectKRestrict_id]

/-- Inverse-affine restriction of the original coefficient pullback is the first summand. -/
theorem nativeCoefficientFirst_inverse_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (nativeAffineIso R).inv n).comp
        (perfectKFlatPullback (projection R) n) =
      KMap (nativeFirstSummand_exact (affineBase R)) n := by
  ext a
  exact (congrArg (perfectKRestrict (nativeAffineIso R).inv n)
    (DFunLike.congr_fun (nativeCoefficientFirst_transport R n) a)).symm.trans
      (DFunLike.congr_fun (nativeCoefficientAffine_restrict_cancel R n)
        (KMap (nativeFirstSummand_exact (affineBase R)) n a))

/-- The original coefficient tensor becomes the second native summand under inverse transport. -/
theorem nativeCoefficientSecond_inverse_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (nativeAffineIso R).inv n).comp
        ((tautologicalCoefficientTensorKMap R n).comp
          (perfectKFlatPullback (projection R) n)) =
      KMap (nativeSecondSummand_exact (affineBase R)) n := by
  ext a
  exact (congrArg (perfectKRestrict (nativeAffineIso R).inv n)
    (DFunLike.congr_fun (nativeCoefficientSecond_transport R n) a)).symm.trans
      (DFunLike.congr_fun (nativeCoefficientAffine_restrict_cancel R n)
        (KMap (nativeSecondSummand_exact (affineBase R)) n a))

/-- Negative-chart restriction of the actual projective pullback is the polynomial coefficient. -/
theorem nativeCoefficient_minusChart_pullback (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (minusChart R) n).comp (perfectKFlatPullback (projection R) n) =
      polynomialCoefficientKMap R n := by
  rw [← perfectKFlatPullback_eq_restrict, ← perfectKFlatPullback_comp]
  simp only [minusChart_projection, polynomialCoefficientKMap]

/-- Every original coefficient cone has the actual forward Phi coordinates (a, a inverse). -/
theorem nativeCoefficientConeForget_phi (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (Spec R) n) :
    perfectSupportedKMap (positiveOpen R).ι n
        (nativeTautologicalCoefficientConeKMap R n (perfectKFlatPullback (projection R) n a)) =
      nativeTwoSummandKMap (affineBase R) n (a, a⁻¹) := by
  calc
    _ = perfectKRestrict (nativeAffineIso R).inv n (perfectKFlatPullback (projection R) n a) *
        (perfectKRestrict (nativeAffineIso R).inv n
          (tautologicalCoefficientTensorKMap R n (perfectKFlatPullback (projection R) n a)))⁻¹ :=
      nativeCoefficientConeForget_apply R n _
    _ = KMap (nativeFirstSummand_exact (affineBase R)) n a *
        (KMap (nativeSecondSummand_exact (affineBase R)) n a)⁻¹ :=
      congrArg₂ (fun x y => x * y⁻¹)
        (DFunLike.congr_fun (nativeCoefficientFirst_inverse_transport R n) a)
        (DFunLike.congr_fun (nativeCoefficientSecond_inverse_transport R n) a)
    _ = _ := by rw [nativeTwoSummandKMap_apply, map_inv]

attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- The full actual cone homomorphism has its original two forward Phi coordinates. -/
theorem nativeCoefficientConeForget_comp_phi (R : CommRingCat.{u}) (n : ℕ) :
    ((perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n)).comp
          (perfectKFlatPullback (projection R) n) =
      (nativeTwoSummandKMap (affineBase R) n).comp
        ((MonoidHom.id (PerfectK (Spec R) n)).prod invMonoidHom) := by
  ext a
  exact nativeCoefficientConeForget_phi R n a

/-- The original unit boundary retains the forward Phi image (a inverse, a) on every input. -/
theorem nativeCoefficientSelfTrackBoundary_phi (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (Spec R) n) :
    laurentProjectiveConnecting R n
      (originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
          (polynomialCoefficientKMap R n a)) =
      nativeTwoSummandKMap (affineBase R) n (a⁻¹, a) := by
  have h := laurentProjectiveConnecting_selfTrack_coefficient_allDegrees R n
    (perfectKFlatPullback (projection R) n a)
  have hi : perfectKRestrict (minusChart R) n (perfectKFlatPullback (projection R) n a) =
      polynomialCoefficientKMap R n a :=
    DFunLike.congr_fun (nativeCoefficient_minusChart_pullback R n) a
  rw [hi] at h
  refine h.trans ?_
  rw [nativeCoefficientConeForget_phi, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

/-- The whole coefficient boundary map is the original Phi after its signed diagonal. -/
theorem nativeCoefficientSelfTrackBoundary_comp_phi (R : CommRingCat.{u}) (n : ℕ) :
    (laurentProjectiveConnecting R n).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n).comp
          (polynomialCoefficientKMap R n)) =
      (nativeTwoSummandKMap (affineBase R) n).comp
        (invMonoidHom.prod (MonoidHom.id (PerfectK (Spec R) n))) := by
  ext a
  exact nativeCoefficientSelfTrackBoundary_phi R n a

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
