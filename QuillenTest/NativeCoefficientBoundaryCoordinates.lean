/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientBoundaryCoordinates

/-! # Strict clients of the original native coefficient boundary coordinates -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProjectiveLine Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.NativeCoefficientBoundaryCoordinates
open FlasqueTwoSummands

/-- Both literal Boolean trivializations retain the original minus/plus chart order. -/
theorem original_boolean_trivializations (R : CommRingCat.{u}) (b : Bool) :
    lineChartIso R b = ((fun c => by
      cases c
      · exact tautologicalLineMinusIso R
      · exact tautologicalLinePlusIso R) :
        (c : Bool) → (tautologicalLine R).restrict (polynomialChart R c) ≅
          SheafOfModules.unit (Spec (CommRingCat.of (Polynomial R))).ringCatSheaf) b :=
  coefficientTensor_lineChartIso R b

/-- The complete tensor functor agrees before passing to K-maps. -/
theorem original_tensor_functor (R : CommRingCat.{u}) :
    tautologicalCoefficientTensorFunctor R = localNegativeTwist R :=
  coefficientTensorFunctor_eq_localNegativeTwist R

/-- The first original summand transports as a full homomorphism. -/
theorem original_first_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKFlatPullback (nativeAffineIso R).hom n).comp
        (KMap (nativeFirstSummand_exact (affineBase R)) n) =
      perfectKFlatPullback (projection R) n :=
  nativeCoefficientFirst_transport R n

/-- The second original summand retains the full actual line-tensor map. -/
theorem original_second_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKFlatPullback (nativeAffineIso R).hom n).comp
        (KMap (nativeSecondSummand_exact (affineBase R)) n) =
      (tautologicalCoefficientTensorKMap R n).comp
        (perfectKFlatPullback (projection R) n) :=
  nativeCoefficientSecond_transport R n

/-- The two actual affine maps cancel on all original native classes. -/
theorem original_affine_cancellation (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (nativeAffineIso R).inv n).comp
        (perfectKFlatPullback (nativeAffineIso R).hom n) =
      MonoidHom.id (PerfectK (nativeLineFunctor.obj (affineBase R)).obj n) :=
  nativeCoefficientAffine_restrict_cancel R n

/-- Inverse restriction recovers the original first native K-map. -/
theorem original_first_inverse_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (nativeAffineIso R).inv n).comp
        (perfectKFlatPullback (projection R) n) =
      KMap (nativeFirstSummand_exact (affineBase R)) n :=
  nativeCoefficientFirst_inverse_transport R n

/-- Inverse restriction recovers the original second native K-map. -/
theorem original_second_inverse_transport (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (nativeAffineIso R).inv n).comp
        ((tautologicalCoefficientTensorKMap R n).comp
          (perfectKFlatPullback (projection R) n)) =
      KMap (nativeSecondSummand_exact (affineBase R)) n :=
  nativeCoefficientSecond_inverse_transport R n

/-- The actual negative chart yields the complete polynomial coefficient homomorphism. -/
theorem original_polynomial_input (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKRestrict (minusChart R) n).comp (perfectKFlatPullback (projection R) n) =
      polynomialCoefficientKMap R n :=
  nativeCoefficient_minusChart_pullback R n

/-- Every original coefficient gives the forward cone Phi coordinates. -/
theorem arbitrary_original_cone (R : CommRingCat.{u}) (n : ℕ) (a : PerfectK (Spec R) n) :
    perfectSupportedKMap (positiveOpen R).ι n
        (nativeTautologicalCoefficientConeKMap R n (perfectKFlatPullback (projection R) n a)) =
      nativeTwoSummandKMap (affineBase R) n (a, a⁻¹) :=
  nativeCoefficientConeForget_phi R n a

/-- The perfect K-groups carry the commutative group structure used by these tests. -/
local instance perfectKCommGroup (X : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK X n) :=
  Additivity.KCommGroup (perfectWaldhausen X) n

/-- The full cone homomorphism uses the original signed diagonal. -/
theorem original_cone_hom (R : CommRingCat.{u}) (n : ℕ) :
    ((perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n)).comp
          (perfectKFlatPullback (projection R) n) =
      (nativeTwoSummandKMap (affineBase R) n).comp
        ((MonoidHom.id (PerfectK (Spec R) n)).prod invMonoidHom) :=
  nativeCoefficientConeForget_comp_phi R n

/-- The whole boundary homomorphism retains the original unit and forward Phi map. -/
theorem original_boundary_hom (R : CommRingCat.{u}) (n : ℕ) :
    (laurentProjectiveConnecting R n).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n).comp
          (polynomialCoefficientKMap R n)) =
      (nativeTwoSummandKMap (affineBase R) n).comp
        (invMonoidHom.prod (MonoidHom.id (PerfectK (Spec R) n))) :=
  nativeCoefficientSelfTrackBoundary_comp_phi R n

/-- Arbitrary connective inputs have the original inverse-first boundary coordinates. -/
theorem arbitrary_original_boundary (R : CommRingCat.{u}) (n : ℕ)
    (a : PerfectK (Spec R) n) :
    laurentProjectiveConnecting R n
      (originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) n
          (polynomialCoefficientKMap R n a)) =
      nativeTwoSummandKMap (affineBase R) n (a⁻¹, a) :=
  nativeCoefficientSelfTrackBoundary_phi R n a

/-- Degree zero retains every original class rather than only a chosen object class. -/
theorem arbitrary_original_kzero (R : CommRingCat.{u}) (a : PerfectK (Spec R) 0) :
    laurentProjectiveConnecting R 0
      (originalKSelfTrackOperation
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectFlatUnitHomotopy (laurentMinus R) (laurentGlobalUnit R)) 0
          (polynomialCoefficientKMap R 0 a)) =
      nativeTwoSummandKMap (affineBase R) 0 (a⁻¹, a) :=
  nativeCoefficientSelfTrackBoundary_phi R 0 a

end QuillenTest.NativeCoefficientBoundaryCoordinates
