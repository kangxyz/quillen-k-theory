/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientConeAdditivity

/-! # Strict clients of the exact native coefficient-cone transport -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProjectiveLine Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.NativeCoefficientConeAdditivity
open FlasqueTwoSummands

/-- The whole functor identity retains the two original support inclusions. -/
theorem original_functor_identity (R : CommRingCat.{u}) :
    nativeTautologicalCoefficientConeFunctor R ⋙
        ObjectProperty.ιOfLE
          (show perfectSupported (positiveOpen R).ι ≤
            locallyPerfect (nativeLineFunctor.obj (affineBase R)).obj from fun _ h => h.1) =
      tautologicalCoefficientForgottenConeFunctor R ⋙ perfectRestrict (nativeAffineIso R).inv :=
  nativeCoefficientForgottenConeFunctor_eq R

/-- An arbitrary coefficient arrow remains the literal original inverse-affine restriction. -/
theorem original_coefficient_arrow (R : CommRingCat.{u})
    {K L : Perfect (twoChartLine R)} (g : K ⟶ L) :
    ((nativeTautologicalCoefficientConeFunctor R).map g).hom =
      (restrict (nativeAffineIso R).inv).map
        ((tautologicalCoefficientConeFunctor R).map g).hom :=
  nativeTautologicalCoefficientConeFunctor_map_hom R g

/-- The actual support-forgetting K-map is the complete original composite. -/
theorem original_composite_hom (R : CommRingCat.{u}) (n : ℕ) :
    (perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n) =
      (perfectKRestrict (nativeAffineIso R).inv n).comp
        ((perfectSupportedKMap (plusChart R) n).comp (tautologicalCoefficientConeKMap R n)) :=
  nativeCoefficientConeForget_comp R n

/-- Arbitrary original inputs retain restriction on both summands. -/
theorem arbitrary_original_input (R : CommRingCat.{u}) (n : ℕ)
    (x : PerfectK (twoChartLine R) n) :
    perfectSupportedKMap (positiveOpen R).ι n (nativeTautologicalCoefficientConeKMap R n x) =
      perfectKRestrict (nativeAffineIso R).inv n x *
        (perfectKRestrict (nativeAffineIso R).inv n
          (tautologicalCoefficientTensorKMap R n x))⁻¹ :=
  nativeCoefficientConeForget_apply R n x

/-- The same formula includes arbitrary K-zero classes without object representatives. -/
theorem arbitrary_original_kzero (R : CommRingCat.{u}) (x : PerfectK (twoChartLine R) 0) :
    perfectSupportedKMap (positiveOpen R).ι 0 (nativeTautologicalCoefficientConeKMap R 0 x) =
      perfectKRestrict (nativeAffineIso R).inv 0 x *
        (perfectKRestrict (nativeAffineIso R).inv 0
          (tautologicalCoefficientTensorKMap R 0 x))⁻¹ :=
  nativeCoefficientConeForget_apply R 0 x

/-- The native projective-line K-groups carry their canonical commutative group structure. -/
local instance nativeLinePerfectKCommGroup (R : CommRingCat.{u}) (n : ℕ) :
    CommGroup (PerfectK (nativeLineFunctor.obj (affineBase R)).obj n) :=
  Quillen.Waldhausen.Additivity.KCommGroup
    (perfectWaldhausen (nativeLineFunctor.obj (affineBase R)).obj) n

/-- The entire original homomorphism keeps its native target and actual inverse-affine map. -/
theorem original_native_difference_hom (R : CommRingCat.{u}) (n : ℕ) :
    (perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n) =
      perfectKRestrict (nativeAffineIso R).inv n *
        (invMonoidHom.comp ((perfectKRestrict (nativeAffineIso R).inv n).comp
          (tautologicalCoefficientTensorKMap R n))) :=
  nativeCoefficientConeForget_hom R n

end QuillenTest.NativeCoefficientConeAdditivity
