/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientConeAdditivity
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoefficientConeFunctor

/-! # The original native coefficient cone difference

The actual supported native cone, followed by support forgetting, is the original local cone
followed by inverse-affine restriction as an equality of functors. Original K-map composition
transports the local all-degree cone difference without changing that geometric restriction.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open FlasqueTwoSummands

/-- Both complete functors retain the same original restricted cone objects and arrows. -/
theorem nativeCoefficientForgottenConeFunctor_eq (R : CommRingCat.{u}) :
    nativeTautologicalCoefficientConeFunctor R ⋙
        ObjectProperty.ιOfLE
          (show perfectSupported (positiveOpen R).ι ≤
            locallyPerfect (nativeLineFunctor.obj (affineBase R)).obj from fun _ h => h.1) =
      tautologicalCoefficientForgottenConeFunctor R ⋙ perfectRestrict (nativeAffineIso R).inv :=
  rfl

/-- The actual native support-forgetting map is the original local cone then restriction. -/
theorem nativeCoefficientConeForget_comp (R : CommRingCat.{u}) (n : ℕ) :
    (perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n) =
      (perfectKRestrict (nativeAffineIso R).inv n).comp
        ((perfectSupportedKMap (plusChart R) n).comp (tautologicalCoefficientConeKMap R n)) := by
  calc
    _ = KMap ((nativeTautologicalCoefficientConeFunctor_waldhausenExact R).comp
        (subcategoryInclusion_exact (perfectSupported (positiveOpen R).ι)
          (locallyPerfect (nativeLineFunctor.obj (affineBase R)).obj) (fun _ h => h.1))) n :=
      KMap_comp_KMap (nativeTautologicalCoefficientConeFunctor_waldhausenExact R)
        (subcategoryInclusion_exact (perfectSupported (positiveOpen R).ι)
          (locallyPerfect (nativeLineFunctor.obj (affineBase R)).obj) (fun _ h => h.1)) n
    _ = KMap ((tautologicalCoefficientForgottenConeFunctor_waldhausenExact R).comp
        (perfectRestrict_waldhausenExact (nativeAffineIso R).inv)) n :=
      KMap_eq_of_iso _ _ (eqToIso (nativeCoefficientForgottenConeFunctor_eq R)) n
    _ = (perfectKRestrict (nativeAffineIso R).inv n).comp
        (KMap (tautologicalCoefficientForgottenConeFunctor_waldhausenExact R) n) :=
      (KMap_comp_KMap (tautologicalCoefficientForgottenConeFunctor_waldhausenExact R)
        (perfectRestrict_waldhausenExact (nativeAffineIso R).inv) n).symm
    _ = _ := congrArg
      (fun z : PerfectK (twoChartLine R) n →* PerfectK (twoChartLine R) n =>
        (perfectKRestrict (nativeAffineIso R).inv n).comp z)
      (tautologicalCoefficientForgottenCone_KMap R n).symm

/-- Every native cone class retains inverse-affine restriction on both original summands. -/
theorem nativeCoefficientConeForget_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : PerfectK (twoChartLine R) n) :
    perfectSupportedKMap (positiveOpen R).ι n (nativeTautologicalCoefficientConeKMap R n x) =
      perfectKRestrict (nativeAffineIso R).inv n x *
        (perfectKRestrict (nativeAffineIso R).inv n
          (tautologicalCoefficientTensorKMap R n x))⁻¹ :=
  calc
    _ = perfectKRestrict (nativeAffineIso R).inv n
        (perfectSupportedKMap (plusChart R) n (tautologicalCoefficientConeKMap R n x)) :=
      DFunLike.congr_fun (nativeCoefficientConeForget_comp R n) x
    _ = _ := by rw [tautologicalCoefficientConeKMap_forget, map_mul, map_inv]

attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- The full native homomorphism is the original affine restriction difference. -/
theorem nativeCoefficientConeForget_hom (R : CommRingCat.{u}) (n : ℕ) :
    (perfectSupportedKMap (positiveOpen R).ι n).comp
        (nativeTautologicalCoefficientConeKMap R n) =
      perfectKRestrict (nativeAffineIso R).inv n *
        (invMonoidHom.comp ((perfectKRestrict (nativeAffineIso R).inv n).comp
          (tautologicalCoefficientTensorKMap R n))) := by
  ext x
  exact nativeCoefficientConeForget_apply R n x

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
