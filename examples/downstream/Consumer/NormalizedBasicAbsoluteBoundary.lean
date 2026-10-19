/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicOriginalBoundary

/-!
# Exactness of the intrinsic basic boundary on original absolute groups

For a compact quasi-separated scheme and a compact open, original restriction
is exact before the intrinsic basic boundary in every nonpositive degree.
The actual identity-open projection and independent original class maps are
retained, and the actual supported class isomorphism transports exactness.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterNormalizedBasicLocalization
open Quillen.PerfectComplexes.Bass Quillen.PerfectComplexes.Bass.SupportedLocalization
namespace Consumer.NormalizedBasicAbsoluteBoundary
universe u
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
attribute [local instance] basicOriginalPair_source_compact basicOriginalPair_target_quasiSeparated

private theorem exact_postcompose_iso {A B C D : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (e : C ≅ D) (hex : Function.Exact f g) :
    Function.Exact f (g ≫ e.hom) :=
  hex.comp_injective e.hom e.addCommGroupIsoToAddEquiv.injective (map_zero e.hom.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original absolute restriction is exact before the intrinsic normalized basic boundary. -/
theorem original_negative_exactness (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] (i : ℕ) :
    Function.Exact
      (negativeKPullback (ObjectProperty.homMk U.ι :
        (⟨U.toScheme, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj (basicOriginalPair Q U)) i)
      ((identityOpenGroupIso (basicOriginalPair Q U) i).hom ≫
        GlobalParameterCoefficient.normalizedRowNegativeClass
          (Over.mk (toIntegerBase U.toScheme)) i identityCoefficient ≫
        (negativeLocalizationDegreeIso i).hom.app
          (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (op integerBase)) ≫
        basicConnecting Q U (-((i + 1 : ℕ) : ℤ))) := by
  have : IsIso (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
      (basicOverInclusion Q U) (i + 1) identityCoefficient) :=
    basicNormalizedNegativeClass_isIso Q U (i + 1) identityCoefficient
  rw [basicConnecting_original_negative_square]
  exact exact_postcompose_iso _ _
    ((identitySupportGroupIso (basicOriginalPair Q U) (i + 1)) ≪≫
      asIso (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (basicOverInclusion Q U) (i + 1) identityCoefficient))
    (supportedNegativeLocalizationConnecting_exact_open (basicOriginalPair Q U) i)

end Consumer.NormalizedBasicAbsoluteBoundary
