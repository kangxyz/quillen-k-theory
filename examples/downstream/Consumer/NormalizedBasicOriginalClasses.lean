/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicNegativeBoundary

/-! # Exactness through the original classes of the intrinsic basic row -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterNormalizedBasicLocalization
namespace Consumer.NormalizedBasicOriginalClasses
universe u
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
attribute [local instance] GlobalSupportedParameterCoefficient.normalizedRowNegativeClass_isIso
attribute [local instance] basicNormalizedNegativeClass_isIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The independently defined basic boundary is exact after the original negative restriction. -/
theorem original_negative_exactness (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI := basicNormalizedNegativeClass_isIso Q U (i + 1) a
    Function.Exact
      ((boundedFlatCoefficientOriginalNegativeKRestriction (basicOverInclusion Q U) i).app a)
      (GlobalParameterCoefficient.normalizedRowNegativeClass
          (Over.mk (toIntegerBase U.toScheme)) i a ≫
        (negativeLocalizationDegreeIso i).hom.app
          (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (specUnder.obj a)) ≫
        basicSpecConnecting Q U a (-((i + 1 : ℕ) : ℤ)) ≫
        inv (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
          (basicOverInclusion Q U) (i + 1) a)) := by
  rw [basicNegativeConnecting_eq_original]
  exact boundedFlatCoefficientNegativeLocalizationConnecting_exact_open
    (basicOverInclusion Q U) i a

end Consumer.NormalizedBasicOriginalClasses
