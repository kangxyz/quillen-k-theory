/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicOriginalBoundary

/-!
# The intrinsic basic boundary kills the original absolute restriction

For a compact quasi-separated scheme and a compact open, the degree-zero
original restriction has zero composite with the intrinsic basic boundary.
The actual identity projection, original normalized class and degree cast
remain in the composite; the original groups are not replaced by coefficients.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterNormalizedBasicLocalization
open Quillen.PerfectComplexes.Bass Quillen.PerfectComplexes.Bass.SupportedLocalization
namespace QuillenTest.NormalizedBasicAbsoluteBoundary
universe u
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
attribute [local instance] basicOriginalPair_source_compact basicOriginalPair_target_quasiSeparated

private theorem exact_comp_post_zero {A B C D : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (hex : Function.Exact f g) :
    f ≫ g ≫ h = 0 := by
  ext x
  change h (g (f x)) = 0
  rw [hex.apply_apply_eq_zero]
  exact map_zero h.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Original absolute K₀ restriction is killed by the intrinsic degree-minus-one boundary. -/
theorem original_zero_restriction_boundary (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] :
    negativeKPullback (ObjectProperty.homMk U.ι :
        (⟨U.toScheme, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj (basicOriginalPair Q U)) 0 ≫
      (identityOpenGroupIso (basicOriginalPair Q U) 0).hom ≫
      GlobalParameterCoefficient.normalizedRowNegativeClass
        (Over.mk (toIntegerBase U.toScheme)) 0 identityCoefficient ≫
      (negativeLocalizationDegreeIso 0).hom.app
        (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (op integerBase)) ≫
      basicConnecting Q U (-((0 + 1 : ℕ) : ℤ)) = 0 := by
  rw [basicConnecting_original_negative_square]
  exact exact_comp_post_zero _ _ _
    (supportedNegativeLocalizationConnecting_exact_open (basicOriginalPair Q U) 0)

end QuillenTest.NormalizedBasicAbsoluteBoundary
