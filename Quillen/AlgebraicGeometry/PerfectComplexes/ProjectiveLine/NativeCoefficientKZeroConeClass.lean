/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientCoordinate
public import Quillen.Waldhausen.SplitComplexes.MappingConeKZeroRelation

/-! # Original native K-zero coordinates of arbitrary coefficient cones -/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
variable (X : QuasiCompactSchemes.{u})

/-- Forgetting support keeps the signed cone difference on every original perfect object. -/
theorem coefficientSupportedCone_forget_class (K : Perfect (nativeLineFunctor.obj X).obj) :
    perfectSupportedKMap (positiveOpen X).ι 0
      ((perfectSupportedWaldhausen (positiveOpen X).ι).kZeroObjectClass
        (coefficientSupportedCone X K)) =
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass K *
        ((perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass
          ((nativeNegativeTwist X).obj K))⁻¹ := by
  exact (KMap_kZeroObjectClass
    (subcategoryInclusion_exact (perfectSupported (positiveOpen X).ι)
      (locallyPerfect _) (fun _ h => h.1)) (coefficientSupportedCone X K)).trans
        (SplitFactorization.subcategoryCone_kZeroObjectClass (locallyPerfect _)
          (fun hK hL g => locallyPerfect_mappingCone hK hL g)
          (coefficientPerfectCoordinate X K))

/-- The actual coefficient cone has the original native Phi coordinates on every K-zero object.
-/
theorem coefficientSupportedCone_forget_phi (K : Perfect X.obj) :
    perfectSupportedKMap (positiveOpen X).ι 0
      ((perfectSupportedWaldhausen (positiveOpen X).ι).kZeroObjectClass
        (coefficientSupportedCone X ((nativeFirstSummand X).obj K))) =
      nativeTwoSummandKMap X 0
        ((perfectWaldhausen X.obj).kZeroObjectClass K,
          ((perfectWaldhausen X.obj).kZeroObjectClass K)⁻¹) := by
  rw [coefficientSupportedCone_forget_class, nativeTwoSummandKMap_apply, map_inv,
    KMap_kZeroObjectClass, KMap_kZeroObjectClass]
  rfl

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
